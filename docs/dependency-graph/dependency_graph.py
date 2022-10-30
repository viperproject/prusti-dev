#!/usr/bin/env python3
import os
import re
import itertools
from pathlib import Path
from graphviz import Digraph

cwd = Path(os.getcwd()).parts
BASE_PATH = cwd
while not os.path.isfile(os.path.join(*BASE_PATH, "Cargo.toml")):
    BASE_PATH = BASE_PATH[:-1]
BASE_PATH = os.path.join(*BASE_PATH)

# search for registered Cargo.toml and packages in the project
workspaces = [
    BASE_PATH,
    os.path.join(BASE_PATH, "prusti-contracts"),
]
members = {}

for workspace in workspaces:
    with open(os.path.join(workspace, "Cargo.toml")) as f:
        while True:
            line = f.readline()
            if not line:
                break
            line = line.strip()

            if line.endswith(","):
                line = line[:-1]

            if line.startswith("\"") and line.endswith("\""):
                name = line[1:-1]
                cargo_toml_path = os.path.join(workspace, name, "Cargo.toml")
                readme_path = os.path.join(workspace, name, "README.md")
                if not os.path.isfile(cargo_toml_path):
                    print(f"Path '{cargo_toml_path}' doesn't exist")
                    cargo_toml_path = None
                if not os.path.isfile(readme_path):
                    print(f"Path '{readme_path}' doesn't exist")
                    readme_path = None
                members[name] = {
                    "cargo_toml": cargo_toml_path,
                    "readme": readme_path,
                }


def parse_description(readme_path):
    if readme_path is None:
        return ""
    with open(readme_path) as f:
        lines = f.readlines()
        # remove title
        lines = itertools.dropwhile(lambda l: l.strip(), lines)
        # remove empty lines after the title
        lines = itertools.dropwhile(lambda l: not l.strip(), lines)
        # take the first paragraph
        lines = itertools.takewhile(lambda l: l.strip(), lines)
        return "".join(lines)


def parse_workspace_dependencies(cargo_toml_path):
    dependencies = set()
    if cargo_toml_path is None:
        return dependencies
    with open(cargo_toml_path) as f:
        while True:
            line = f.readline()
            if not line:
                break
            line = line.strip()

            # a [dependencies] section start
            if line in ("[dependencies]", "[dev-dependencies]", "[build-dependencies]"):
                while True:
                    line = f.readline()
                    if not line or "=" not in line:
                        break
                    line = line.strip()
                    dep = line.split("=")[0].strip()
                    if dep in members:
                        dependencies.add(dep)

    return dependencies


# parse dependencies of Cargo.toml
for name in list(members.keys()):
    member = members[name]
    member["description"] = parse_description(member["readme"])
    member["dependencies"] = parse_workspace_dependencies(member["cargo_toml"])

# generate graph
graph = Digraph(graph_attr={"rankdir": "BT", "nodesep":"0.5", "ranksep":"1"})

for name, member in members.items():
    # word wrap description
    description = member["description"].replace("\n", " ")
    description = "<BR/>".join(
        line.strip()
        for line in re.findall(r".{1,60}(?:\s+|$)", description)
    )
    graph.node(name,
        f'<<FONT FACE="sans-serif bold" POINT-SIZE="16">{name}</FONT><BR/>{description}>',
        shape="box",
        style="filled",
        fillcolor="lightblue2",
    )

for name in members.keys():
    for dependency_name in members[name]["dependencies"]:
        graph.edge(name, dependency_name)

graph.render("prusti_dependencies.gv", view=True)
