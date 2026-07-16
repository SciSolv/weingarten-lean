#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Generate the blueprint dependency graph (PDF + PNG) from content.tex.

Parses the theorem-like environments and their ``\\uses`` annotations in
``blueprint/src/content.tex``, builds the dependency DAG (an edge ``A -> B``
means "B uses A"), lays it out in layers by longest-path depth with a few
barycentre sweeps to reduce edge crossings, and renders it with matplotlib.

Self-contained: networkx + matplotlib only -- no graphviz, no LaTeX. This is a
local, committed substitute for the interactive leanblueprint web graph; the
underlying data is the same ``\\uses`` annotations the GitHub Pages site uses.

  python scripts/gen_dep_graph.py
"""
import os
import re
import collections
import networkx as nx
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "blueprint", "src", "content.tex")
OUT_DIR = os.path.join(ROOT, "docs")

NODE_ENVS = ["theorem", "proposition", "lemma", "corollary", "definition", "remark"]
KIND_COLOR = {
    "theorem": "#cfe8ff", "proposition": "#cfe8ff", "lemma": "#cfe8ff",
    "corollary": "#cfe8ff", "definition": "#d9f7d0", "remark": "#fff0cc",
}


def parse(text):
    """label -> {kind, uses(set), leanok(bool)}; span = this env begin .. next env begin."""
    begins = [(m.start(), m.group(1)) for m in
              re.finditer(r"\\begin\{(" + "|".join(NODE_ENVS) + r")\}", text)]
    nodes = {}
    for i, (pos, env) in enumerate(begins):
        end = begins[i + 1][0] if i + 1 < len(begins) else len(text)
        span = text[pos:end]
        lm = re.search(r"\\label\{([^}]+)\}", span)
        if not lm:
            continue
        label = lm.group(1)
        uses = set()
        for um in re.finditer(r"\\uses\{([^}]+)\}", span):
            uses.update(u.strip() for u in um.group(1).split(",") if u.strip())
        nodes[label] = {"kind": env, "uses": uses,
                        "leanok": "\\leanok" in span, "mathlibok": "\\mathlibok" in span}
    return nodes


def layered_layout(G):
    while not nx.is_directed_acyclic_graph(G):
        cyc = next(nx.simple_cycles(G))
        G.remove_edge(cyc[-1], cyc[0])
        print("warning: removed cycle edge %s -> %s" % (cyc[-1], cyc[0]))
    layer = {n: 0 for n in G.nodes()}
    for n in nx.topological_sort(G):
        for p in G.predecessors(n):
            layer[n] = max(layer[n], layer[p] + 1)
    order = collections.defaultdict(list)
    for n in G.nodes():
        order[layer[n]].append(n)
    for L in order:
        order[L].sort()
    xpos = {}

    def assign():
        for L, ns in order.items():
            k = len(ns)
            for i, n in enumerate(ns):
                xpos[n] = i - (k - 1) / 2.0

    assign()
    Ls = sorted(order)
    for _ in range(8):
        for L in Ls[1:]:
            order[L].sort(key=lambda n: sum(xpos[p] for p in G.predecessors(n))
                          / max(1, G.in_degree(n)))
            assign()
        for L in reversed(Ls[:-1]):
            order[L].sort(key=lambda n: sum(xpos[s] for s in G.successors(n))
                          / max(1, G.out_degree(n)))
            assign()
    pos = {n: (xpos[n] * 2.4, -layer[n] * 1.8) for n in G.nodes()}
    return pos, max(len(ns) for ns in order.values()), len(order)


def main():
    with open(SRC, encoding="utf-8") as f:
        text = f.read()
    nodes = parse(text)
    G = nx.DiGraph()
    G.add_nodes_from(nodes)
    for label, d in nodes.items():
        for u in d["uses"]:
            if u in nodes:
                G.add_edge(u, label)

    pos, maxw, nlayers = layered_layout(G)
    leanok = sum(1 for d in nodes.values() if d["leanok"])
    print("nodes=%d edges=%d layers=%d maxwidth=%d leanok=%d/%d"
          % (G.number_of_nodes(), G.number_of_edges(), nlayers, maxw, leanok, len(nodes)))
    nonok = sorted(l for l, d in nodes.items() if not d["leanok"])
    print("non-leanok nodes (%d): %s" % (len(nonok), ", ".join(nonok)))
    fig, ax = plt.subplots(figsize=(min(60, max(14, maxw * 2.3)),
                                    min(40, max(9, nlayers * 1.7))))
    for u, v in G.edges():
        (x1, y1), (x2, y2) = pos[u], pos[v]
        ax.annotate("", xy=(x2, y2), xytext=(x1, y1),
                    arrowprops=dict(arrowstyle="-|>", color="#aaaaaa", lw=0.5,
                                    shrinkA=11, shrinkB=11))
    for n in G.nodes():
        x, y = pos[n]
        ax.text(x, y, n, fontsize=5.5, ha="center", va="center", zorder=3,
                bbox=dict(boxstyle="round,pad=0.28",
                          fc=KIND_COLOR.get(nodes[n]["kind"], "#eeeeee"),
                          ec=("#2b6cb0" if nodes[n]["leanok"]
                              else "#2e8b57" if nodes[n]["mathlibok"] else "#999999"),
                          lw=0.8))
    from matplotlib.patches import Patch
    ax.legend(handles=[
        Patch(fc="#cfe8ff", ec="#444444", label="theorem / proposition / lemma / corollary"),
        Patch(fc="#d9f7d0", ec="#444444", label="definition"),
        Patch(fc="#fff0cc", ec="#444444", label="remark"),
        Patch(fc="white", ec="#2b6cb0", label="blue border = Lean-verified (leanok)"),
        Patch(fc="white", ec="#2e8b57", label="green border = Mathlib-provided (mathlibok)"),
        Patch(fc="white", ec="#999999", label="grey border = prose (no proof obligation)"),
    ], loc="lower right", fontsize=8, framealpha=0.9)
    ax.set_title("weingarten-lean - blueprint dependency graph  "
                 "(%d nodes, %d edges; theorem-class nodes Lean-verified)"
                 % (G.number_of_nodes(), G.number_of_edges()), fontsize=11)
    ax.axis("off")
    xs = [p[0] for p in pos.values()]
    ys = [p[1] for p in pos.values()]
    ax.set_xlim(min(xs) - 2.5, max(xs) + 2.5)
    ax.set_ylim(min(ys) - 1.5, max(ys) + 1.5)
    os.makedirs(OUT_DIR, exist_ok=True)
    fig.savefig(os.path.join(OUT_DIR, "dependency_graph.pdf"), bbox_inches="tight")
    try:
        fig.savefig(os.path.join(OUT_DIR, "dependency_graph.png"), dpi=50)
        print("png ok")
    except Exception as e:
        print("png skipped (%s)" % e)


if __name__ == "__main__":
    main()
