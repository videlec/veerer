r"""
Labelled directed graphs and fundamental group
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024 Vincent Delecroix
#
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License
#  as published by the Free Software Foundation; either version 2
#  of the License, or (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
# ****************************************************************************

import collections

from sage.graphs.digraph import DiGraph
from sage.misc.prandom import choice, randrange


class LabelledDiGraph:
    r"""
    Small overlay over a digraph so that vertices and labels gets labells from
    0 to n-1 and 0 to m-1 respectively.


    EXAMPLES::

        sage: from veerer.labelled_digraph import LabelledDiGraph, LabelledDiGraphPath
        sage: G = LabelledDiGraph(digraphs.ButterflyGraph(5), sort=True)
        sage: G.vertex_label(3)
        ('00000', 3)
        sage: G.vertex_index(('00000', 3))
        3
        sage: G.outgoing_edges(3)
        [7, 6, -5, -45]
        sage: G.incoming_edges(3)
        [4, 44, -8, -7]
    """
    def __init__(self, digraph, root=None, sort=False):
        self._digraph = DiGraph(len(digraph), loops=digraph.allows_loops(), multiedges=digraph.allows_multiple_edges())

        self._vertices = list(digraph)
        if sort:
            self._vertices.sort()
        if root is not None:
            i = self._vertices.index(root)
            self._vertices[0], self._vertices[i] = self._vertices[i], self._vertices[0]
        self._vertex_index = {v: i for i, v in enumerate(self._vertices)}

        self._edge_sources = []
        self._edge_targets = []
        self._edge_labels = []

        edges = list(digraph.edges())
        if sort:
            edges.sort()
        for k, (u, v, label) in enumerate(edges):
            i = self._vertex_index[u]
            j = self._vertex_index[v]
            self._edge_sources.append(i)
            self._edge_targets.append(j)
            self._edge_labels.append(label)
            self._digraph.add_edge(i, j, k)

    def __repr__(self):
        return "LabelledDiGraph on {} vert{} and {} edge{}".format(self.num_verts(), "ex" if self.num_verts() <= 1 else "ices",
                                                                   self.num_edges(), "" if self._edge_sources else "s")
    def num_verts(self):
        return len(self._vertices)

    __len__ = num_verts

    def num_edges(self):
        return len(self._edge_sources)

    def vertex_label(self, i):
        return self._vertices[i]

    def edge_label(self, i):
        return self._edge_labels[i] if i >= 0 else self._edge_labels[~i]

    def vertex_index(self, v):
        return self._vertex_index[v]

    def edge_source(self, i):
        r"""
        TESTS::

            sage: from veerer.labelled_digraph import LabelledDiGraph, LabelledDiGraphPath
            sage: G = LabelledDiGraph(digraphs.ButterflyGraph(5), sort=True)
            sage: for e in range(G.num_edges()):
            ....:     assert G.edge_source(e) == G.edge_target(~e)
            ....:     assert G.edge_source(~e) == G.edge_target(e)
        """
        i = int(i)
        if i >= 0:
            return self._edge_sources[i]
        else:
            return self._edge_targets[~i]

    def edge_target(self, i):
        i = int(i)
        if i >= 0:
            return self._edge_targets[i]
        else:
            return self._edge_sources[~i]

    def outgoing_edges(self, i, reverse=True):
        r"""
        TESTS::

            sage: from veerer.labelled_digraph import LabelledDiGraph, LabelledDiGraphPath
            sage: G = LabelledDiGraph(digraphs.ButterflyGraph(5), sort=True)
            sage: for v in range(G.num_verts()):
            ....:     assert all(G.edge_source(e) == v for e in G.outgoing_edges(v))
            ....:     assert all(G.edge_target(e) == v for e in G.incoming_edges(v))
        """
        ans = [label for _, _, label in self._digraph.outgoing_edges(i)]
        if reverse:
            ans.extend(~label for _, _, label in self._digraph.incoming_edges(i))
        return ans

    def incoming_edges(self, i, reverse=True):
        ans = [label for _, _, label in self._digraph.incoming_edges(i)]
        if reverse:
            ans.extend(~label for _, _, label in self._digraph.outgoing_edges(i))
        return ans

    def spanning_tree(self, root=0):
        r"""
        Return a pair ``(tree, complementary_edges)`` that form a spanning
        tree of this labelled digraph.

        EXAMPLES::

            sage: from veerer.labelled_digraph import LabelledDiGraph
            sage: G = LabelledDiGraph(digraphs.ButterflyGraph(5), sort=True)
            sage: tree, edges = G.spanning_tree()
            sage: tree[0] is None
            True
            sage: any(x is None for x in tree[1:])
            False
            sage: len(tree) + len(edges) - 1 == G.num_edges()
            True
        """
        tree = [None] * len(self)  # tree[vertex] = edge to follow to go to the root
        complementary_edges = []
        seen = [False] * len(self)
        seen[root] = True
        todo = [root]
        while todo:
            v = todo.pop()
            for i in self.incoming_edges(v):
                u = self.edge_source(i)
                if not seen[u]:
                    tree[u] = i
                    seen[u] = True
                    todo.append(u)
                elif i >= 0 and tree[v] != ~i:
                    complementary_edges.append(i)
        return tree, complementary_edges

    def path(self, start, edges=None):
        return LabelledDiGraphPath(self, start, edges)

    def fundamental_group_basis(self, root=0):
        r"""
        Iterate through a basis of the fundamental group of the digraph ``G``.

        EXAMPLES::

            sage: from veerer.labelled_digraph import LabelledDiGraph
            sage: G = LabelledDiGraph(digraphs.DeBruijn(2, 3), sort=True)
            sage: for path in G.fundamental_group_basis():
            ....:     print(path)
            Path of length 1 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[0]
            Path of length 3 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[-9, 9, -2]
            Path of length 7 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[1, 3, 7, 15, -8, -4, -2]
            Path of length 7 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[1, 3, 7, 14, -7, -4, -2]
            Path of length 6 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[1, 2, 5, 11, -4, -2]
            Path of length 7 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[1, 3, 6, 13, 11, -4, -2]
            Path of length 6 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[1, 3, -12, 10, -3, -2]
            Path of length 4 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[1, 2, 4, 8]
            Path of length 5 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=0 made of edges=[1, 3, 6, 12, 8]
        """
        tree, complementary_edges = self.spanning_tree(root)
        for i in complementary_edges:
            path = LabelledDiGraphPath(self, self.edge_source(i))
            path.append(i)

            v = path.start()
            while v != root:
                i = tree[v]
                path.appendleft(~i)
                v = self.edge_target(i)

            v = path.end()
            while v != root:
                i = tree[v]
                path.append(i)
                v = self.edge_target(i)

            yield path


class LabelledDiGraphPath:
    r"""
    Path in a labelled digraph.

    EXAMPLES::

        sage: from veerer.labelled_digraph import LabelledDiGraph, LabelledDiGraphPath
        sage: G = LabelledDiGraph(digraphs.ButterflyGraph(5), sort=True)
        sage: path = LabelledDiGraphPath(G, 0)
        sage: path.append(0)
        sage: path.append(-161)
        sage: path.appendleft(-2)
        sage: path.appendleft(-163)
        sage: path
        Path of length 4 in LabelledDiGraph on 192 vertices and 320 edge from start=98 to target=96 made of edges=[-163, -2, 0, -161]
    """
    def __init__(self, graph, start, edges=None):
        self._graph = graph
        self._vertices = collections.deque([start])  # vertices
        self._edges = collections.deque([])          # edge labels (>= 0 for forward and < 0 for backward)

        if edges is not None:
            for i in edges:
                self.append(i)

    def copy(self):
        ans = type(self).__new__(type(self))
        ans._vertices = self._vertices[:]
        ans._edges = self._edges[:]
        return ans

    def __bool__(self):
        return bool(self._edges)

    def __len__(self):
        return len(self._edges)

    def __iter__(self):
        return iter(self._edges)

    def __repr__(self):
        return "Path of length {} in {} from start={} to target={} made of edges={}".format(len(self), self._graph, self.start(), self.end(), list(self._edges))

    def start(self):
        return self._vertices[0]

    def end(self):
        return self._vertices[-1]

    def __invert__(self):
        ans = self.copy()
        ans._vertices.reverse()
        ans._edges.reverse()
        for i, j in ans._edges:
            ans[i] = ~j

    def __mul__(self, other):
        if type(self) != type(other):
            raise TypeError
        if self._graph is not other._graph:
            raise ValueError("path on different graphs")
        if self.end() != other.start():
            raise ValueError("incompatible paths: the end of the first path must be the start of the second one")

        ans = self.copy()
        ans._vertices.extend(other._vertices[1:])
        ans._edges.extend(other._edges)
        return ans

    def append(self, i):
        r"""
        Append the i-th edge to the right of the path.
        """
        i = int(i)
        if i >= 0:
            source = self._graph._edge_sources[i]
            target = self._graph._edge_targets[i]
        else:
            source = self._graph._edge_targets[~i]
            target = self._graph._edge_sources[~i]
        if source != self._vertices[-1]:
            raise ValueError("invalid edge i={}".format(i))
        self._vertices.append(target)
        self._edges.append(i)

    def random_append(self, repeat=1, reverse=True):
        r"""
        EXAMPLES::

            sage: from veerer.labelled_digraph import LabelledDiGraph, LabelledDiGraphPath
            sage: G = LabelledDiGraph(digraphs.DeBruijn(2, 3), sort=True)
            sage: path = LabelledDiGraphPath(G, 0)
            sage: path.random_append(10)
            sage: path
            Path of length 10 in LabelledDiGraph on 8 vertices and 16 edge from start=0 to target=... made of edges=[...]

            sage: path = LabelledDiGraphPath(G, 0)
            sage: path.random_append(100, reverse=True)
            sage: path.is_oriented()
            False

            sage: path = LabelledDiGraphPath(G, 0)
            sage: path.random_append(100, reverse=False)
            sage: path.is_oriented()
            True
        """
        for _ in range(repeat):
            edges = self._graph.outgoing_edges(self.end(), reverse=reverse and randrange(2))
            if not edges:
                print("dead end at {}".format(self.end()))
            self.append(choice(edges))

    def pop(self):
        r"""
        Pop the last edge of the path and return ``(source, target, edge_label)``.
        """
        if not self:
            raise IndexError("pop from an empty path")
        target = self._vertices.pop()
        edge = self._edges.pop()
        return (self.end(), target, edge)

    def appendleft(self, i):
        r"""
        Append an edge on the left.
        """
        i = int(i)
        if i >= 0:
            source = self._graph._edge_sources[i]
            target = self._graph._edge_targets[i]
        else:
            source = self._graph._edge_targets[~i]
            target = self._graph._edge_sources[~i]
        if target != self._vertices[0]:
            raise ValueError("invalid edge")
        self._vertices.appendleft(source)
        self._edges.appendleft(i)

    def random_appendleft(self, repeat=1, reverse=True):
        r"""
        EXAMPLES::

            sage: from veerer.labelled_digraph import LabelledDiGraph, LabelledDiGraphPath

            sage: G = LabelledDiGraph(digraphs.DeBruijn(2, 3), sort=True)
            sage: path = G.path(0)
            sage: path.random_appendleft(10)
            sage: path
            Path of length 10 in LabelledDiGraph on 8 vertices and 16 edge from start=... to target=0 made of edges=[...]

            sage: path = LabelledDiGraphPath(G, 0)
            sage: path.random_appendleft(100, reverse=True)
            sage: path.is_oriented()
            False

            sage: path = LabelledDiGraphPath(G, 0)
            sage: path.random_appendleft(100, reverse=False)
            sage: path.is_oriented()
            True
        """
        for _ in range(repeat):
            edges = self._graph.incoming_edges(self.start(), reverse=reverse and randrange(2))
            if not edges:
                raise ValueError("dead end at {}".format(self.start()))
            self.appendleft(choice(edges))

    def popleft(self):
        r"""
        Pop the first edge of the path and return ``(source, target, edge_label)``.
        """
        if not self:
            raise IndexError("pop from an empty path")
        source = self._vertices.popleft()
        edge = self._edges.popleft()
        return (source, self.start(), edge)

    def is_oriented(self):
        r"""
        Return whether the path is oriented.

        A path is *oriented* if it follows each edge orientation.

        EXAMPLES::

            sage: from veerer.labelled_digraph import LabelledDiGraph

            sage: G = LabelledDiGraph(digraphs.DeBruijn(2, 3), sort=True)
            sage: G.path(2).is_oriented()
            True
            sage: G.path(0, [1, 2, 5, 10, 4]).is_oriented()
            True
            sage: G.path(0, [0, 1, -10, 8]).is_oriented()
            False
        """
        return all(edge >= 0 for edge in self._edges)

    def is_closed(self):
        r"""
        Return whether the path is closed.

        A path is *closed* if it starts and ends at the same vertex.

        EXAMPLES::

            sage: from veerer.labelled_digraph import LabelledDiGraph

            sage: G = LabelledDiGraph(digraphs.DeBruijn(2, 3), sort=True)
            sage: G.path(2).is_closed()
            True
            sage: G.path(0, [0]).is_closed()
            True
            sage: G.path(0, [-9, 9, 2, -11, 10, 5, 11, 7, 14, 12, 8]).is_closed()
            True
            sage: G.path(0, [1, 2, 5, 10, 4]).is_closed()
            False
        """

        return self.start() == self.end()

    # TODO: should maybe be called is_reduced?
    def is_non_backtracking(self):
        r"""
        Return whether the path is non-backtracking.

        A path is *non-backtracking* if it does not contain as a sub-path an
        edge followed by its inverse.

        EXAMPLES::

            sage: from veerer.labelled_digraph import LabelledDiGraph

            sage: G = LabelledDiGraph(digraphs.DeBruijn(2, 3), sort=True)
            sage: G.path(2).is_non_backtracking()
            True
            sage: G.path(0, [1, 2, -3]).is_non_backtracking()
            False
        """
        return all(self._edges[i] != ~self._edges[i + 1] for i in range(len(self._edges) - 1))
