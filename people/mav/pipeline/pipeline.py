from urllib.parse import urlparse
import argparse
import inspect
from collections import defaultdict
import copy
import glob
import logging
import os
import hashlib
import pprint
import shutil
import re
import sys
import time
import yaml
import tempfile
from autologging import traced

from rich import pretty
from rich.console import Console
from rich.table import Table
from rich import box
from rich.syntax import Syntax
from rich.rule import Rule
from rich.text import Text
from rich.logging import RichHandler
from rich.tree import Tree
from rich import print
from rich.panel import Panel

from pygments import highlight
from pygments.lexers import PythonLexer
from pygments.formatters import Terminal256Formatter
from pprint import pformat

from functools import cache
import cmd2
import json
from jsonschema import validators #Draft202012Validator as metavalidator
from jsonschema import validate, RefResolver
from jsonschema.exceptions import best_match

import networkx as nx
import networkx.drawing as nxd
import matplotlib.pyplot as plt
from networkx.readwrite import json_graph
from matplotlib import style

import matplotlib
#matplotlib.use('GTK3Cairo') #'tkagg' )
matplotlib.use('svg') #'tkagg' )


style.use("ggplot")

from PIL import Image

console = Console()
FORMAT = "%(message)s"
logging.basicConfig(
    level="ERROR", format=FORMAT, datefmt="[%X]", handlers=[RichHandler(markup=True)]
)
log = logging.getLogger("pipeline")

def load_json(path):
#    log.debug(f"READING [bold purple]{path}[/]")
    if ".yaml" in path:
        with open(path, "r") as f:
            return yaml.safe_load(f)
    else:
        log.error(path)
        assert False
        return json.load(f)


def schema_handler(path):
    url = urlparse(path)
    log.debug(f"Loading schema [bold purple]{url.path}[/]")
    return load_schema(url.path)

def get_validator(schema):
    resolver = RefResolver("", {}, handlers={"schema" : schema_handler})
    return validators.validator_for(schema)

@cache
def load_schema(path):
    schema = load_json(path)
    get_validator(schema).check_schema(schema)
    return schema

def get_kind(component):
    if component and 'kind' in component:
        return component["kind"]
    else:
        return None

def open_arity(ports):
    return next((item for item in ports if item.get("arity") == "_"), None)

def is_fanout(component):
    return open_arity(component.get('outputs', []))

def is_fanin(component):
#    print(f'**** is_fanin inputs: {[(i["name"], i.get("arity")) for i in component.get("inputs", [])]}')
    # the following are both needed as inputs on fanin docuemnts are modified, when we do we leave a flag
    # to say that the component is a  fanin point
    return component.get("fanin", open_arity(component.get('inputs', [])))

def is_group(component):
    return get_kind(component) == "group"

def is_task(component):
    return get_kind(component) == "task"

def is_include(component):
    return get_kind(component) == "include"

def subcomponents(component):
    return component and component['components'] if is_group(component) else []


def find_component_aux(component, path):
#    log.error(f'{component} {path}')
    try:
        this, rest = path.split('.', 1)
    except:
        this = path
        rest = None

    if component["name"] != this:
#        log.error(f'Returning None None')
        return None

    if is_group(component):
        for subcomponent in component.get("components", []):
            component = find_component_aux(subcomponent, rest)
            if component:
#               log.error(f'Returning 1 {rest}')
                return component
#    log.error(f'Returning 2 {component} {rest}')
    return component

def find_component_aux1(component, path):
    try:
        this, rest = path.split('.', 1)
    except:
        this = path
        rest = None

#    log.error(f'**** {component} **** ||{path}|| - {this} {rest}')

    if component["name"] != this:
#        log.error(f'Name mismatch, returning None None')
        return None, None

    if is_group(component):
#        log.error('DOING SUBCOMPONENTS')
        for subcomponent in component.get("components", []):
            component, rest1 = find_component_aux1(subcomponent, rest)
            if component:
 #               log.error(f'Returning 1 {rest}')
                return component, rest1
#    log.error(f'Returning 2 {component} {rest}')
    return component, rest

def relative_component_path(component, path):
    return find_component_aux1(component, path)[1]

def find_component(component, path):
    return find_component_aux(component, path)

def find_component_for_output(component, path):
    component_path, output_name = path.rsplit('.', 1)
    component = find_component(component, component_path)
    if component is None:
        return None
    if "outputs" in component:
        for output in component['outputs']:
            if output["name"] == output_name:
                return component
    return None

def find_output(component, path):
    rest, output_name = path.rsplit('.', 1)
    c = find_component_for_output(component, path)
    assert c, f"Component containing {path} not found"
    for o in c.get('outputs', []):
        if o['name'] == output_name:
            return o
    raise Exception(f'output {path} not found')

def maybe_expand_include(component, root, context):
#    log.error(f"Maybe expand include in {component} @ {root} contest: {context} ")

    if is_include(component):
        path = component["source"]
        definition = load_definition(path, root)
        definition["name"] = f'{component["name"]}'
        for c in component.get("parameters", []):
            for k,v in c.items():
                this = context.rsplit('.',1)[1]
                absolute_key = f'{this}.{k}'
#                log.error(f'config key: {absolute_key} value: {v}')
                inner_component = find_component(definition, k)
#                log.error(f'inner {inner_component}')
                c,r = find_component_aux1(definition, absolute_key)
#                log.error(f'******** COMP AND REST {c} {r}')
                if r == 'image':
                    c['image'] = v
                if r.startswith('config'):
                    _, config = r.split('.', 1)
                    c['config'][config] = v
                    # we mark things as modified just to add a config node when displaying graphs
                    c['modified'] = True
            # relative_path = relative_component_path(definition, k)
            # log.error(f'Setting config {k} for {inner_component.get("name")} at {relative_path}')

            # assert inner_component, f'Cannot find {k} in {definition}'
#             inner_component["config"] = v
 #       log.debug(f"  result: [blue]{definition}[/]")
        return definition
    else:
#        log.debug("propagating component")
#        log.debug(f"  *** result: [blue]{component}[/]")
        return component

def expand_definition(definition, root, context):
    if is_group(definition):
        definition["components"] = [expand_definition(c, root, f'{context}.{c["name"]}') for c in definition["components"]]
        return definition
    else:
        return maybe_expand_include(definition, root, context)

def load_definition(path, root):
    log.debug(f"Loading definition [bold purple]{path}[/]")
    definition = load_json(root + '/' + path)

    schema = load_schema("people/mav/pipeline/schemas/component.yaml")
    resolver = RefResolver("", {}, handlers={"schema" : schema_handler})
    try:
        validators.validator_for(schema)(schema, resolver=resolver).validate(definition)
    except:
        log.error(best_match(validators.validator_for(schema)(schema, resolver=resolver).iter_errors(definition)).message)

    return expand_definition(definition, root, definition['name'])

def values(value_list):
    formatted_values = []
    for v in value_list:
        connection = f' ({v["reference"]})' if "reference" in v else ''
        array = '[]' if 'arity' in v and v['arity'] == '_' else ''
        formatted_values.append(f'{v["name"]}[[blue]{v["value_type"]}{array}[/blue]]{connection}')
    return ", ".join(formatted_values)

def dump_pipeline_aux(tree, el):
    config_colors = [
        "yellow1",
        "dark_orange",
        "orchid2",
        "light_steel_blue",
        "deep_pink4",
        "bright_magenta",
        "green4",
        "dark_olive_green3"
    ]
    if is_group(el):
        group = tree.add(f':sparkles: [bold blue]{el["name"]}[/]', style="dim")
        for sub_el in el["components"]:
            dump_pipeline_aux(group, sub_el)
    else:
        inputs = values(el["inputs"]) if "inputs" in el else ""
        outputs = values(el["outputs"]) if "outputs" in el else ""
        configuration = f'c{el["config"]}' if "config" in el else "c?"
        try:
            color = config_colors[el["config"] % len(config_colors)]
        except:
            color="white"
        image = f'{el.get("image","master")}'
        tree.add(#Table(
            f':gear: [{color}]{configuration}[/{color}]@{image} [green]{el["name"]}[/] {inputs} :arrow_right: {outputs}')
        #)

def dump_pipeline(el):
    tree = Tree("Pipeline", guide_style="grey50")
    dump_pipeline_aux(tree, el)
    print(tree)

# def fix_input_references(component, context):
#     # here we do something incorrect, we assume that if something can be
#     # found relative to this component then is a relative path needing
#     # fixing. In reaity we'll invent a syntax for absolute paths
#     for i in component["inputs"]:
#         if find_component_for_output(component

def fix_references_aux(parent, component, context):
#    log.error(f'fix_references_aux({parent["name"]}, {component["name"]}, {context})')
    for i in component.get('inputs', []):
        out_parent = find_component_for_output(parent, f'{parent["name"]}.{i["reference"]}')
        if out_parent:
#            log.error(f'**** FIXING {i["reference"]} TO {context}.{i["reference"]}')
            i['reference'] = f'{context}.{i["reference"]}'
            i['producer'] = out_parent
#        else:
#            log.error(f'**** not found {i["reference"]} in {parent}')
    if is_group(component):
        for subcomponent in component["components"]:
            fix_references_aux(component, subcomponent, f'{context}.{component["name"]}')

#    fix_references_aux(component, f'{context}') #.{component["name"]}')

def fix_references(component):
#    log.error(f'fix_references({component["name"]})')
    if is_group(component):
        for subcomponent in component["components"]:
            fix_references_aux(component, subcomponent, component['name'])

def add_modified_config_nodes(g):
    modified = []
    for n, c in g.nodes(data=True):
        if c['component'].get('modified', False):
            modified += [(f'{n}-config', n)]

    for c, n in modified:
        g.add_node(c, fillcolor='black', style='filled', label="")
        g.add_edge(c, n, arrowhead='none', arrowtail='none')

def display_graph(g, label):
    gg = g.copy()
    add_modified_config_nodes(gg)

    graph_file = tempfile.NamedTemporaryFile(suffix='.png')
    A = nx.nx_agraph.to_agraph(gg)
    A.graph_attr["label"] = label
    A.node_attr["shape"] = "box"
    A.edge_attr["color"] = "red"
    A.node_attr["colorscheme"] = "paired12"
    A.layout(prog="dot")
    A.draw(graph_file.name)
    im = Image.open(graph_file.name)
    im.show()
    graph_file.close()

def path_complete(
        self, text: str, line: str, begidx: int, endidx: int
    ):
    root_dir = f'repo/{self.persona}/head'
    matches = glob.glob(f"{text}*.yaml", root_dir=root_dir)
    matches += ['labels.yaml']
    return matches

def component_targets(component):
    if is_task(component):
        return [f'{component["name"]}.{i["name"]}' for i in component['outputs']]
    targets = []
    for s in subcomponents(component):
        targets += [f'{component["name"]}.{sn}' for sn in component_targets(s)]

    return targets

def target_complete(
        self, text: str, line: str, begidx: int, endidx: int
    ):


    targets = []
    commit = self.personas[self.persona]["commit"]
    commit_cache = self.definition_cache[self.persona][str(commit)]
    for f,c in commit_cache.items():
        targets += [t for t in component_targets(c) if t.startswith(text)]
    return targets

#     for f in
#         targets = [ f.removesuffix('.yaml')+'.' for f in files if f.startswith(text)]

#     if '.' not in text:
#         commit = self.personas[self.persona]["commit"]
#         files = self.definition_cache[self.persona][str(commit)]
#         targets = [ f.removesuffix('.yaml')+'.' for f in files if f.startswith(text)]
# #        log.error(f'***** {targets}')
#         return targets

#     if text.endswith("."):
#         top_component = text.split('.',1)[0]
#         return [f'{text}.{a}' for a in ['1','2','3']]



#    return ['a', 'b']
    # root_dir = f'repo/{self.persona}/head'
    # matches = glob.glob(f"{text}*.yaml", root_dir=root_dir)
    # return matches

class CAS:

    def __init__(self):
        self.content = {}

    def reset(self):
        self.content = {}

    def put(self, index, value):
        self.content[index] = value

    def get(self, index):
        return self.content.get(index)

    def dump(self):
        print()
        if len(self.content) == 0:
            print('[dim italic white]Nothing to see here, move along[/]\n')
            return

        global console

        table = Table(title = 'Content-Addressable Storage', show_header=True, header_style="bold magenta", box=box.SIMPLE_HEAVY)
        table.add_column("sha", style="dim", width=12)
        table.add_column("content")

        for k, v in self.content.items():
            table.add_row(k[:8].decode(), Syntax(str(v), 'python', theme='ansi_dark'))
        #     print(f'[bold red]{k[:8]}[/]\t[italic white]{v}[/]')

        # for id, l in self.labels.items():
        #     table.add_row(id, ", ".join(l['tags']), ", ".join(l['labels']))

        console.print(table)


base_parser = cmd2.Cmd2ArgumentParser()
become_parser = cmd2.Cmd2ArgumentParser() # base_parser.add_parser('become', help='Change persona')
become_parser.add_argument('persona', type=str, choices=["asok", "wally", "ci"]) #self.personas.keys())

class MotionPlanningREPL(cmd2.Cmd):
    """A simple cmd2 application."""
    def __init__(self):
        super().__init__(persistent_history_file="~/.pipeline")

        self.cas = CAS()

        self.definition_cache = defaultdict(lambda: defaultdict(dict))

        self.persona = "asok"

        self.mp_tag = 1

        # self.labels = {
        #     "L1": {
        #         "tags": ["train", "c1", "gold"],
        #         "labels": ["lc"],
        #     },
        #     "L2": {
        #         "tags": ["train", "c1", "gold"],
        #         "labels": ["lc","y"],
        #     },
        #     "L3": {
        #         "tags": ["train", "c2", "gold"],
        #         "labels": ["lc"],
        #    },
        #     "L4": {
        #         "tags": ["train", "c2", "gold"],
        #         "labels": ["lc"],
        #     },
        #     "L5": {
        #         "tags": ["test", "c1", "gold"],
        #         "labels": ["lc"],
        #     },
        #     "L6": {
        #         "tags": ["test", "c2", "gold"],
        #         "labels": ["lc"],
        #     }
        # }
        self.personas = {
            "ci": {
                "description": "The continuous integration dude",
                "commit": 1
            },
            "wally": {
                "description": "The do-nothing engineer",
                "commit": 1
            },
            "asok": {
                "description": "The intern",
                "commit": 1
            }
        }
        self.images = {}

        # Make maxrepeats settable at runtime
        self.maxrepeats = 3
        self.add_settable(cmd2.Settable('debug', bool, 'Trace progress for debug', self))
        del cmd2.Cmd.do_edit
        del cmd2.Cmd.do_py
        del cmd2.Cmd.do_run_pyscript

        self.register_preloop_hook(self.intro_hook)

        self.set_prompt()
        self.reset_state()
        self.refresh_cache()
#        self.cache_stats()

        self.register_precmd_hook(self.precommand_hook)
#        self.register_postparsing_hook(self.postparsing_hook)

    # def postparsing_hook(self, params: cmd2.plugin.PostparsingData) -> cmd2.plugin.PostparsingData:
    #     print(params.statement.raw)
    #     # if 'as' in params.statement.raw:
    #     #     newinput = params.statement.raw + ' | less'
    #     params.statement = self.statement_parser.parse("labels_list")
    #     return params

    # as_parser = cmd2.Cmd2ArgumentParser()
    # as_parser.add_argument(
    #     'user', nargs=argparse.OPTIONAL, help="The user we want to run as" , choices = self.personas.keys()
    # )
    # get_parser.add_argument(
    #     'cmd', nargs=argparse.OPTIONAL, help="The command" ,
    # )
    # @cmd2.with_argparser(get_parser)
    # def do_as(self, args):
    #     pass

    def intro_hook(self) -> None:
        col = [
            'dark_violet', # 'blue3',
            'medium_orchid', #'dark_blue',
            'light_steel_blue', #'blue1',
            'grey89', #'deep_sky_blue4',

            'bold orange3'
        ]
        intro = f"""

[{col[0]}] __  __  _____  ____  ____  _____  _  _    ____  __      __    _  _  _  _  ____  _  _  ___
[{col[1]}](  \/  )(  _  )(_  _)(_  _)(  _  )( \( )  (  _ \(  )    /__\  ( \( )( \( )(_  _)( \( )/ __)
[{col[2]}] )    (  )(_)(   )(   _)(_  )(_)(  )  (    )___/ )(__  /(__)\  )  (  )  (  _)(_  )  (( (_-.
[{col[3]}](_/\/\_)(_____) (__) (____)(_____)(_)\_)  (__)  (____)(__)(__)(_)\_)(_)\_)(____)(_)\_)\___/

[{col[4]}]B O L D L Y   T R A I N I N G    M O D E L S    N O B O D Y    T R A I N E D    B E F O R E[/]

                   :sparkles: [grey69]Welcome to the Motion Planning shell.[/] :sparkles:

[dim cyan]Type 'help' to list commands. <TAB> or '?' will autocomplete commands.[/]

"""
        print(intro)
        return

    def precommand_hook(self, data: cmd2.plugin.PrecommandData) -> cmd2.plugin.PrecommandData:
        if self.quiet:
            log.setLevel("ERROR")
        else:
#            log.setLevel("DEBUG")
            log.setLevel("TRACE")

        self.load_labels()

        # the statement object created from the user input
        # is available as data.statement
        return data

    def commit_head(self, persona):
        shutil.copytree(f'repo/{persona}/head', f'repo/{persona}/{self.personas[persona]["commit"]}')

    def load_labels(self):
        label_file = f'repo/{self.persona}/{self.personas[self.persona]["commit"]}/globals/labels.yaml'
#        with open('people/mav/pipeline/labels.yaml', "r") as f:
        with open(label_file, "r") as f:
            self.labels = yaml.safe_load(f)

    def reset_state(self):
        self.images = {}
        self.cas.reset()
        if os.path.isdir('repo'):
            shutil.rmtree('repo')
        for p in self.personas.keys():
            os.makedirs(f'repo/{p}', exist_ok=True)
            shutil.copytree('people/mav/pipeline/definitions', f'repo/{p}/head')
            os.makedirs(f'repo/{p}/head/globals', exist_ok=True)
            shutil.copyfile('people/mav/pipeline/labels.yaml', f'repo/{p}/head/globals/labels.yaml')
            self.personas[p]["commit"] = 1
            self.commit_head(p)
        self.load_labels()

    # TASKS
    def task_generate(self, config):
        result = []
#        print(self.labels)
        for name, label in self.labels.items():
            if config['labels'] in label['tags']:
                label['log'] = name
                result.append(label)
        return result

    def task_snippet(self, config, snippet):
        result = { "kind": "log", "source": snippet['log'] }
        return result

    def task_t1_extract(self, config, log):
        result = { "kind": "table", "source": log}
        return result

    def task_t2_extract(self, config, log):
        result = { "kind": "table", "source": log}
        return result

    def task_t1_aggregate(self, config, table):
        # for t in table:
        #     print(f'===== {t} =====')

        result = { "kind": "table", "source": [t["source"] for t in table] }
        return result

    def task_t2_aggregate(self, config, table):
        result = { "kind": "table", "source": [t["source"] for t in table] }
        return result

    def task_m1_training(self, config, table):
        result = { "kind": "model", "type": "M1" }
        return result

    def task_m2_training(self, config, table):
        result = { "kind": "model", "type": "M2" }
        return result

    def task_m1_eval(self, config, model, table):
        result = "The result of evaluating M1"
        return result

    def task_m2_eval(self, config, model, table):
        result = "The result of evaluating M2"
        return result

    def task_m1_digest(self, config, result_pr, result_mp):
        result = 'A digest of M1 a/b comparison'
        return result

    def task_m2_digest(self, config, result_pr, result_mp):
        result = 'A digest of M2 a/b comparison'
        return result


#    edit_completer = functools.partial(path_complete, persona = self.persona)
    edit_parser = cmd2.Cmd2ArgumentParser()
    edit_parser.add_argument(
        'file_path', nargs=argparse.OPTIONAL, help="optional path to a file to open in editor" , completer=path_complete #edit_completer
    )
    @cmd2.with_argparser(edit_parser)
    def do_edit(self, args: argparse.Namespace) -> None:
        """Run a text editor and optionally open a file with it"""

        dir_path = f"repo/{self.persona}/head/"
        file_path = args.file_path
        if file_path == 'labels.yaml':
            dir_path = dir_path + '/globals/'
        # self.last_result will be set by do_shell() which is called by run_editor()
        self.run_editor(dir_path + file_path)


    # become_parser.set_defaults(func=become)
    # label_parser_bar.set_defaults(func=label)

    def do_labels_list(self, args):
        global console

        def color_tag(tag):
            if tag == 'gold':
                return '[gold1]gold[/]'
            elif tag == 'train':
                return '[plum2]train[/]'
            elif tag == 'test':
                return '[light_slate_blue]test[/]'
            else:
                return tag

        table = Table(title = 'Labels', show_header=True, header_style="bold magenta", box=box.SIMPLE_HEAVY)
        table.add_column("ID", style="dim", width=12)
        table.add_column("tags")
        table.add_column("labels")

        for id, l in sorted(self.labels.items()):
            table.add_row(id, ", ".join([color_tag(t) for t in l['tags']]), ", ".join(l['labels']))

        console.print(table)


    @cmd2.with_argparser(become_parser)
    def do_become(self, args):
        self.persona = args.persona
        self.refresh_cache()

    def do_reset(self, args):
        self.reset_state()

    # TODO with subcommands, this will be 'commit land' and 'commit list'
    def do_commit(self, args):
        self.personas[self.persona]["commit"] += 1
        self.commit_head(self.persona)
        self.refresh_cache

    def do_stats(self, arguments):
        self.cache_stats()

    def do_tag(self, arguments):
        self.mp_tag = self.personas['ci']['commit']

    def do_commits(self, args):
        global console

        table = Table(title = 'Commits', show_header=True, header_style="bold magenta", box=box.SIMPLE_HEAVY)
        table.add_column("Persona", style="dim", width=12)
        table.add_column("Commit")

        for n, p in self.personas.items():
            table.add_row(n, f'{n[0]}{p["commit"]}')

        console.print(Rule())
        console.print(table)
        console.print(Rule())

    #cmd2.with_argparser(base_parser)
    def do_label(self, args):
        global console

        table = Table(title = 'Demo Labels', show_header=True, header_style="bold magenta", box=box.SIMPLE_HEAVY)
        table.add_column("ID", style="dim", width=12)
        table.add_column("Tags")
        table.add_column("Labels")

        for l,d in self.labels.items():
            table.add_row(l, " ".join(d["tags"]), " ".join(d["labels"]))

        console.print(table)

    def simplify_graph_aux(self, top_component, current_component, current_path, visited):
        if is_task(current_component):
            visited[current_path] = True
            for i in current_component.get('inputs', []):
                reference = i.get('reference')
                assert reference, f'Unconnected input {i.name}'
                component_path, _ = reference.rsplit('.', 1)

                self.simplify_graph_aux(top_component,
                                        find_component_for_output(top_component, reference),
                                        component_path,
                                        visited)

        if is_group(current_component):
            log.error('OPPSIE')
            raise Exception('is_group unsupported')
        #     for c in current_component.get('components', []):
        #         self.simplify_graph_aux(top_component, c, , vidited)

    def remove_unused_tasks(self, component, path, needed):
        if not is_group(component):
            return

        l = subcomponents(component)
        l[:] = [c for c in l if f'{path}.{c["name"]}' in needed or is_group(c)]

        for c in subcomponents(component):
            self.remove_unused_tasks(c, f'{path}.{c["name"]}', needed)


    def simplify_graph(self, top_component, target):
        """Return a reduced graph suitable for getting _target_"""
        component = find_component_for_output(top_component, target)
        component_path, _ = target.rsplit('.', 1)

        visited = {}
        self.simplify_graph_aux(top_component, component, component_path, visited)
        self.remove_unused_tasks(top_component, top_component['name'], visited)

        return top_component

    def build_plan(self, component, target):
        pass

    def describe_plan(self, plan, target):
        pass

    def get_task_inputs(self, task):
#        print('-- getting inputs --')

        inputs = {}
        # very ad hoc, we really assume one input on fanout successors
        for i, input in enumerate(task.get('inputs', [])):
            task_index = task.get("index")
            producer = input["producer"]
            hash = self.get_output_hash(producer)
            indexed_result = is_fanout(producer) is not None
#            print(f'{input["name"]} @ {hash}')
            input_value = self.cas.get(hash)
            if is_fanout(producer) is not None:
                inputs[input["name"]] = input_value[task_index]
            else:
#                print(f'**** {task["name"]} is_fanin: {is_fanin(task)}')
                if task.get('fanin', False):
#                    print(f'**** APPENDING {inputs[input["name"]]}')
                    if input["name"] in inputs:
                        inputs[input["name"]].append(input_value)
                    else:
                        inputs[input["name"]] = [input_value]
                else:
                    inputs[input["name"]] = input_value
#        print(inputs)
        return inputs

    def run_task(self, task):
        task_index = task.get('index')
#        print('=== get output_hash (skip test) for {task["name"]} ===')
        output_hash = self.get_output_hash(task)
#        print('=== end output_hash ===')
        task_name = task.get("implementation")

        config = task.get("config")

        inputs = self.get_task_inputs(task)
        # if task["name"] == "t1-aggregate":
        #     print('------')
        #     print(task['name'])
        #     print(inputs)
        #     print('------')

#        if task['name'] == 'snippet:0':
#            print(f'Here, we look for a run with hash {output_hash}, index: {task_index}')

                    # if isinstance(result, list):
        #     for i, el in enumerate(result):
        #         self.cas.put(self.get_output_hash(task, i), el)

        result = self.cas.get(output_hash)
        if task.get('volatile', False) or result is None:
            print(f':running: running [bold blue]{task["name"]}[/]')
            implementation = getattr(MotionPlanningREPL, task_name)
            args = {k: None for k in list(inspect.signature(implementation).parameters.keys())[2:]} # skp self and config
            assert args.keys() == inputs.keys(), f"Bad arguments for task {args.keys()} - {inputs.keys()}"
            log.debug(f'Running {task_name} \[image: {task["image"]} config: {config}]')
            result = implementation(self, config, **inputs)
#            print('=== get output_hash (output storage) ===')
            self.record_asset(task, result)
#            print('=== end output_hash ===')
        else:
            print(f':satisfied: [dim]not running [strike blue]{task["name"]}[/] {output_hash}')
            log.debug('Running skipped, reusing cached results')

        deferred_tasks = task.get('deferred_tasks', None)
        if deferred_tasks:
            # TODO fix input-output dependencies, must be on i-th task
            deferred_task_names = [t["name"] for t in deferred_tasks["tasks"]]
            deferred_task_instances = []
            scheduled_deferred_tasks = []
            fanin = deferred_tasks["notify"]
            fanin_inputs = fanin['inputs']
            assert len(fanin_inputs) == 1
            fanin_input_template = copy.deepcopy(fanin_inputs[0])
            fanin['inputs'] = []
            fanin['fanin'] = True
            del fanin_input_template['arity']

            for i, r in enumerate(result):
                # finding producer is probably wrong in general, but it should be okk
                # for these simple linear chains
                for task in deferred_tasks["tasks"]:
                    t = copy.deepcopy(task)
                    t['index'] = i
                    t['name'] = f'{t["name"]}:{i}'
                    # we always store here, otherwise the code needs to be rewrittem
                    deferred_task_instances.append(t)
                    for input in t.get("inputs"):
                        o = input['reference'].rsplit('.',2)
                        if o[1] in deferred_task_names:
                            o[1]=f'{o[1]}:{i}'
                            input['producer'] = deferred_task_instances[-2]
                        input['reference'] = '.'.join(o)
                    if self.cas.get(self.get_output_hash(t)) is None:
                        self.schedule_task(t)
                if self.cas.get(self.get_output_hash(deferred_task_instances[-1])) is None:
                    scheduled_deferred_tasks.append(deferred_task_instances[-1])

#                        print(f'COULD SKIPP SCHEDULING {t["name"]}')
                # here the last in deferred_task_instances is the provicer for the task that needs to be notfied
                # we assume that guy has one input (of open arity) and we replace ir with all expansions here
                new_input = copy.deepcopy(fanin_input_template)
                new_input['producer'] = deferred_task_instances[-1]
                new_input['reference'] = None # complicated to set here and we probably don't need it either
                fanin['inputs'].append(new_input)
#                print(f'**** {fanin["name"]} inputs: {[(i["name"], i["producer"]["name"]) for i in fanin["inputs"]]}')
#            print(f'--- [bold red] {len(fanin["inputs"])} [/] {fanin["inputs"]} [green] {fanin["inputs"][0].keys()} [/] ---')
            print(f':calendar: Adding blockers for {deferred_tasks["notify"]["name"]}: {", ".join([t["name"] for t in scheduled_deferred_tasks])}')
            for t in deferred_task_instances:
                if self.cas.get(self.get_output_hash(t)) is None:
#                    print(f'COULD SKIPP SCHEDULING {t["name"]}')
                    self.run_task(t)

#            print(deferred_tasks.keys())
        if task_name is None:
            self.perror(f'No implementation for task {task["name"]}')
            return


    def get_all_predecessors(self, task):
        return [ i['producer'] for i in task.get('inputs', [])]

    def get_output_hash(self, task, value=None):
        if 'hash' in task:
            return task["hash"]

        digest = hashlib.sha256()
        task_name = task["name"]
        task_config = task.get("config", {})

        # we don't pass vaue any more
        if value is not None:
            digest.update(str(value).encode('utf-8'))


        if task['name'] == "generate":
            digest.update(str(self.labels.items()).encode('utf-8'))

        for k,v in sorted(task_config.items()):
            digest.update(k.encode('utf-8'))
            digest.update(str(v).encode('utf-8'))

        digest.update(task_name.encode('utf-8') )
        digest.update(task['image'].encode('utf-8') )

        hashes = [t['hash'] for t in self.get_all_predecessors(task)]

        for i, hash in enumerate(hashes):
            digest.update(hash)
        hash = digest.hexdigest().encode('utf-8')

        task['hash'] = hash
        return hash

    def record_asset(self, task, result):
        task_index = task.get('index')
        hash = self.get_output_hash(task, result)
        if task['name'] == 'generate':
            print(f'Storing at hash {hash}')
        self.cas.put(hash, result)

    def commit_for_persona(self, persona):
        return f'{persona[0]}{self.personas[persona]["commit"]}'

    def commit_for_current_persona(self):
        return self.commit_for_persona(self.persona)

    def commit_for_master(self):
        return self.commit_for_persona('ci')

    def fix_images(self, component):
        if is_task(component):
            image = component.get('image', 'master')
            if image == 'mp':
                image = f'c{self.mp_tag}'
            elif image == 'pr':
                image = self.commit_for_current_persona()
            elif image == 'master':
                image = self.commit_for_master()
            component['image'] = image

        for c in subcomponents(component):
            self.fix_images(c)

    def extract_images_aux(self, component, images):
        if is_task(component):
            # we're guaranteed to have an 'image' here otherwise is a
            # programmer error and we want to fail with noise and
            # flames
            images.add(component['image'])

        for c in subcomponents(component):
            self.extract_images_aux(c, images)

    def extract_images(self, component):
        images=set()
        self.extract_images_aux(component, images)
        return list(images)

    def ensure_image(self, image):
        if image in self.images:
            print(f':thumbsup: Image [bold blue]{image}[/] availeble')
        else:
            print(f':hammer: Building image [bold blue]{image}[/] and pushing to registry')
            self.images[image] = True

    # need to propagate context. Time for a higher order traversal function
    def task_graph_aux(self, component, path, G):
        if is_task(component):
            i  = component["image"]
            if i == 'master':
                color = 0
            elif i == 'mp':
                color = 1
            elif i == 'pr':
                color = 2
            else:
                color = 3 + int(i[1:]) % 9
            G.add_node(path, fillcolor=color, style='filled', component=component)

        for i in component.get('inputs', []):
            o = find_output(G.graph['root_component'], i['reference'])
            o_arity = o.get("arity", 1)
            i_arity = i.get("arity", 1)

            if o_arity != 1 or i_arity != 1:
                arrowhead = 'none'
                arrowtail = 'none'
                if i_arity == 1:
                    dir = 'back'
                else:
                    dir = 'forward'
                G.add_edge(i['reference'].rsplit('.',1)[0], path, color='gray', arrowhead=arrowhead, arrowtail=arrowtail, penwidth=7, style='bold,tapered', dir=dir)
            else:
                G.add_edge(i['reference'].rsplit('.',1)[0], path, color='gray') # , style='bold')
#            G.add_edge(i['reference'].rsplit('.',1)[0], path, color='gray', arrowhead='diamond', arrowtail='diamond', penwidth=7, style='bold,tapered,back', dir='back')
#            G[i['reference'].rsplit('.',1)[0]][path]['color'] = 'green' # "tab:orange"

        for c in subcomponents(component):
            self.task_graph_aux(c, f'{path}.{c["name"]}', G)

    def task_graph(self, component):
        G = nx.DiGraph()
        G.graph['root_component'] = component
        self.task_graph_aux(component, component['name'], G)
        return G

    def task_blockers(self, task):
        if task.get('wait', False):
            return ['dynamic_dependence']
        blockers = []
        for i in task.get('inputs', []):
            # cheating a bit here, assuming the graph is correct we can get
            # to a component by removing the last piece of a path to an output
            blockers += [i['reference'].rsplit('.',1)[0]]
#        print(blockers)
        return blockers

    def schedule_task(self, task):
        blockers = self.task_blockers(task)
        if blockers:
            if blockers[0] == "dynamic_dependence":
                color = '[bold orange_red1]'
            else:
                color = '[bold blue]'
            status = f':hourglass: blocked on: {color}{", ".join(blockers)}[/]'
        else:
            status = ':zap: ready to run'
        print(f':calendar: Scheduling task [bold blue]{task["name"]}[/] {status}')

    # def is_fanout(self, component):
    #     for o in component.get('outputs', []):
    #         if o.get('arity') == '_':
    #             return True
    #     return False

    # def is_fanin(self, component):
    #     for i in component.get('inputs', []):
    #         if i.get('arity') == '_':
    #             return True
    #     return False

    # def defer_mapreduce(self, g, start, end):
    #     pass

    def find_deferred_segment(self, G, path):
        fanin = None
        fanout = None
        for n in path:
            component = G.nodes[n]['component']
            if is_fanout(component):
                fanout = n
            if is_fanin(component):
                fanin = n
        return fanout, fanin

    def fix_fan(self, G):
        tasks = list(nx.topological_sort(G))

        sink_nodes = [x for x in G.nodes() if G.out_degree(x)==0]
        source_nodes = [x for x in G.nodes() if G.in_degree(x)==0]

        deferred_intervals = set()
        for source, sink in [(source, sink) for sink in sink_nodes for source in source_nodes]:
            for path in nx.all_simple_paths(G, source=source, target=sink):
                fanout, fanin = self.find_deferred_segment(G, path)
                deferred_intervals.add( (fanout, fanin) )

#        pretty.pprint(deferred_intervals)
        for fanout, fanin in deferred_intervals:
            fanout_successors = list(G.successors(fanout))
            assert len(fanout_successors) == 1, "We don't have per-output edges, so this is the best we can do"
            first_deferred = fanout_successors[0]

            fanin_predecessors = list(G.predecessors(fanin))
            assert len(fanin_predecessors) == 1, "We don't have per-input edges, so this is the best we can do"
            last_deferred = fanin_predecessors[0]

            deferred_nodes = list(nx.all_simple_paths(G, source=first_deferred, target=last_deferred))
            assert len(deferred_nodes) == 1, "Something seriously broken, these should be linear paths"
            deferred_nodes = deferred_nodes[0]
            deferred_tasks = [G.nodes[n]['component'] for n in list(deferred_nodes)]

            G.nodes[fanout]['component']['deferred_tasks'] = { 'tasks': deferred_tasks, 'notify': G.nodes[fanin]['component'] }
            G.nodes[fanin]['component']['wait'] = True # wait for deferred tasks

            G.remove_nodes_from(deferred_nodes)
            # add a pseudo edge for a nicer display and topological sorting
            G.add_edge(fanout, fanin, style='dotted', arrowtail='none', arrowhead='none')

    def refresh_cache(self, force=False):
        start = time.time()
        persona = self.persona
        commit = self.personas[persona]["commit"]
        files = f'repo/{persona}/{commit}/*.yaml'
        for f in glob.glob(files):
            f = os.path.basename(f)
            self.definition_cache[persona][str(commit)][f] =  load_definition(f, self.repo_root())

    def cache_stats(self):
        for k in self.definition_cache.keys():
            commits = " ".join(self.definition_cache[k].keys())
#            console.print(f'{k}: {" ".join(self.definition_cache[k].keys())}')
            console.print(f'{k}: {commits}')

    def repo_root(self):
        return f'repo/{self.persona}/{self.personas[self.persona]["commit"]}'

    def current_commit(self):
        return f'{self.persona[0]}{self.personas[self.persona]["commit"]}'

    get_parser = cmd2.Cmd2ArgumentParser()
    get_parser.add_argument(
        'target', nargs=argparse.OPTIONAL, help="The target value we want" , completer=target_complete #edit_completer
    )
    get_parser.add_argument(
        'meta', nargs=argparse.OPTIONAL, help="What to do with target" ,
        choices=["definition", "simple", "run", "plan", "schedule"],
        default="run"
    )
    @cmd2.with_argparser(get_parser)
    def do_get(self, args):
        """Get a MP artefact."""
        target = args.target
        meta = args.meta

        self.load_labels()

        # we have a convention that the filename is EL.yaml where EL is the
        # first iem in the target. This is only for demo/autocompletion purposes
        root = self.repo_root()
        filename = f'{target.split(".",1)[0]}.yaml'
        start = time.time()
        if not os.path.exists(root + '/' + filename):
            self.perror(f"File {filename} doesn't exist in for user {self.persona} at commit {self.current_commit()} ({root})")
            return
        definition = load_definition(filename, root=self.repo_root())
        fix_references(definition)

#        log.error(f'****** {component_targets(definition)} ******')
#        return

        if find_component_for_output(definition, target) is None:
            log.error(definition)
            self.perror(f'Invalid target: {target}')
            return

        if meta == 'definition':
            target = target.split('.', 1)[0]
            dump_pipeline(definition)
            g = self.task_graph(definition)
            display_graph(g, f"Graph for {target}")
            return

        self.fix_images(definition)
        definition = self.simplify_graph(definition, target)

        if meta == 'simple':
            dump_pipeline(definition)
            g = self.task_graph(definition)
            display_graph(g, f"Graph for {target}")
            return

#        console.print(Rule())
#        dump_pipeline(definition)

 #       console.print(Rule())
        g = self.task_graph(definition)

#        tasks = list(nx.topological_sort(g))
#        pretty.pprint(tasks)

        self.fix_fan(g)
        if meta == 'schedule':
            display_graph(g, f"Scheduled graph for {target}")
            return

        console.print(Rule())

        tasks = list(nx.topological_sort(g))

        if meta == 'plan':
            log.error('HERE WE WULD SHOW A PLAN, IF WE HAD ONE')
            return

        images = self.extract_images(definition)
        for i in images:
            self.ensure_image(i)

        for task in tasks:
            task_component = g.nodes[task]['component']
            self.schedule_task(task_component)

        for task_name in tasks:
            t = find_component(definition, task_name)
            if t:
                self.run_task(t)
            else:
                print('skipping')
                log.info(f'Skipping {task_name}')

        console.print(Rule())
        print('[bold red italic]Result[/]')
        print(self.cas.get(self.get_output_hash(find_component(definition, tasks[-1]))))
        console.print(Rule())

        # task = find_component_for_output(definition, target)
        # self.run_task(task)

#        print(self.build_plan(definition, target))

        return


    def do_cas(self, args):
        self.cas.dump()

    def do_list(self, args):
        self.list_personas()

    def list_personas(self):
        global console

        table = Table(title = 'Demo Personas', show_header=True, header_style="bold magenta", box=box.SIMPLE_HEAVY)
        table.add_column("Name", style="dim", width=12)
        table.add_column("Description")

        for name,p in self.personas.items():
            table.add_row(name, p["description"])

        console.print(table)

    def do_status(self,args):
        print('Status of all assets, keyed by commit,config (actually config covers commit)')

    def set_prompt(self):
        self.prompt = f'{self.persona}@{self.persona[0]}{self.personas[self.persona]["commit"]} [mp is c{self.mp_tag}]> '

    def postcmd(self, stop: bool, line: str) -> bool:
        """Hook method executed just after a command dispatch is finished.
        :param stop: if True, the command has indicated the application should exit
        :param line: the command line text for this command
        :return: if this is True, the application will exit after this command and the postloop() will run
        """
        self.set_prompt()
        return stop

if __name__ == "__main__":
    c = MotionPlanningREPL()
    c.debug = True
    c.quiet = True
    sys.exit(c.cmdloop())
