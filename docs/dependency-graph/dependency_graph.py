import os
from pathlib import Path
from graphviz import Digraph

BASE_DIR_NAME = "prusti-dev"

cwd = Path(os.getcwd()).parts
BASE_PATH = os.path.join(*cwd[:cwd.index(BASE_DIR_NAME)+1])

# search for registered Cargo.toml and packages in the project
cargo_tomls = []
packages = []

with open(os.path.join(BASE_PATH, "Cargo.toml")) as f:
    while True:
        line = f.readline()
        if not line:
            break
        line = line.strip()

        if line.endswith(","):
            line = line[:-1]

        if line.startswith("\"") and line.endswith("\""):
            possible_cargo_toml = os.path.join(BASE_PATH, line[1:-1], "Cargo.toml")
            if os.path.isfile(possible_cargo_toml):
                cargo_tomls.append(possible_cargo_toml)
                packages.append(line[1:-1])


def parse_dependencies(cargo_toml):
    dependencies = set()
    with open(cargo_toml) as f:
        while True:
            line = f.readline()
            if not line:
                break
            line = line.strip()

            # a [dependencies] section start
            if line.startswith("[") and line.endswith("]") and "dependencies" in line:
                while True:
                    line = f.readline()
                    if not line or "=" not in line:
                        break
                    line = line.strip()
                    dep = line.split("=")[0].strip()
                    if dep in packages:
                        dependencies.add(dep)

    return dependencies


# parse dependencies of Cargo.toml
nodes = []
for i in range(len(cargo_tomls)):
    nodes.append([packages[i], parse_dependencies(cargo_tomls[i])])

# generate graph
created_nodes = set()
graph = Digraph()
graph.graph_attr["rankdir"] = "BT"

for node in nodes:
    if node[0] not in created_nodes:
        graph.node(node[0], node[0])
        created_nodes.add(node[0])
    for dep in node[1]:
        if dep not in created_nodes:
            graph.node(dep, dep)
            created_nodes.add(dep)
        graph.edge(node[0], dep)

graph.render("prusti_dependencies.gv", view=True)
