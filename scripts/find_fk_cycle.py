#!/usr/bin/env python3
"""
Detect table cycles in foreign-key dependencies.
"""
import sys

import networkx as nx


def main():
    graph = nx.DiGraph()
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith('--'):
            continue

        lhs, rhs = line.split(':')
        left_table, _ = lhs.split('.')
        right_table, _ = rhs.split('.')
        graph.add_edge(left_table.lower(), right_table.lower())

    for cycle in nx.simple_cycles(graph):
        print(cycle)


if __name__ == '__main__':
    main()

