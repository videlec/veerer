r"""
Delaunay-Strebel graph (for prime components).
"""

from sage.graphs.digraph import DiGraph
from sage.misc.prandom import randrange

from .permutation import perm_preimage
from .labelled_digraph import LabelledDiGraph, LabelledDiGraphPath
from .veering_triangulation import VeeringTriangulation
from .strebel_graph import StrebelGraph


class DelaunayStrebelGraph(LabelledDiGraph):
    r"""
    Delaunay-Strebel graph.

    The Delaunay-Strebel graph encodes a decomposition of an irreducible linear
    subvarieties of the moduli space of Abelian or quadratic differentials. The
    subset of vertices of the graph that are ``VeeringTriangulation``
    corresponds to cells. The edges encode some (but not all) adjacencies
    between cells.
    """
    def __init__(self, ds_graph):
        root = min(vt for vt in ds_graph if isinstance(vt, VeeringTriangulation))
        LabelledDiGraph.__init__(self, ds_graph, root)

    def num_veering_states(self):
        return sum(isinstance(state, VeeringTriangulation) for state in self._vertices)

    def num_strebel_states(self):
        return sum(isinstance(state, StrebelGraph) for state in self._vertices)

    def num_flip_transitions(self):
        return sum(label[0] == "flip" for label in self._edge_labels)

    def num_rotation_transitions(self):
        return sum(label[0] == "rotate" for label in self._edge_labels)

    def num_strebel_transitions(self):
        return sum(label[0] == "strebel" for label in self._edge_labels)

    def __str__(self):
        return "Delaunay-Strebel graph on {} vertices and {} edges".format(self.num_verts(), self.num_edges())

    def __repr__(self):
        s = ["Delaunay-Strebel graph of {} made of".format(self._vertices[0])]
        s.append("  {} veering Delaunay states".format(self.num_veering_states()))
        s.append("  {} Strebel states".format(self.num_strebel_states()))
        s.append("  {} flip transitions".format(self.num_flip_transitions()))
        s.append("  {} rotation transitions".format(self.num_rotation_transitions()))
        s.append("  {} Strebel transitions".format(self.num_strebel_transitions()))
        return "\n".join(s)

    def root(self):
        return self._vertices[0]

    # The following is clearly not the optimal strategy. We could have a self-loop
    # that commutes with many other flips. We could delete all such loops but one
    # and still generate.
    # For a self-loop with flip "e" one can look at the connected component of the
    # graph where "e" is not flipped and remove all but one "e loop".
    def commuting_loops_and_squares(self, v):
        r"""
        Return loops and squares at ``v``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,8,~7)(~1,~8,3)(2,7,~6)(~2,~3,4)", "RRRBBBBBB")
        """
        distance2 = {}
        for i0 in self.outgoing_edges(v, reverse=False):
            label0 = self._edge_labels[i0]
            if label0[0] != "flip":
                continue
            edges0 = tuple(label0[1])
            col0 = label0[3]
            relabel = label0[4]
            v1 = self._edge_targets[i0]
            for i1 in self.outgoing_edges(v1, reverse=False):
                label1 = self._edge_labels[i1]
                if label1[0] != "flip":
                    continue
                edges1 = tuple(sorted(perm_preimage(relabel, 2 * e) // 2 for e in label1[1]))
                col1 = label1[3]
                distance2[(edges0, col0, edges1, col1)] = (i0, i1)

        loops = []
        squares = []
        for (edges0, col0, edges1, col1), (i0, i1) in distance2.items():
            key = distance2.get((edges1, col1, edges0, col0))
            if key is None:
                continue
            j0, j1 = key
            assert i0 != j0 and i1 != j1
            if i0 == j1:
                loops.append((j0, j1, i1))
            elif i0 < j0:
                squares.append((i0, i1, j0, j1))

        return (loops, squares)

    def reduced(self):
        r"""
        Return a graph whose fundamental group also generates the fundamental
        group of the underlying stratum.
        """
        kept = [True] * self.num_edges()
        for v in range(self.num_verts()):
            loops, squares = self.commuting_loops_and_squares(v)
            for (i, _, j) in loops:
                if kept[i] and kept[j]:
                    r = randrange(2)
                    if r == 0:
                        kept[i] = False
                    else:
                        kept[j] = False

            for (i0, i1, j0, j1) in squares:
                if kept[i0] and kept[i1] and kept[j0] and kept[j1]:
                    r = randrange(4)
                    if r == 0:
                        kept[i0] = False
                    elif r == 1:
                        kept[i1] = False
                    elif r == 2:
                        kept[j0] = False
                    else:
                        kept[j1] = False

        G = DiGraph(self.num_verts(), loops=self._digraph.allows_loops(), multiedges=self._digraph.allows_multiple_edges())
        for i, b in enumerate(kept):
            if b:
                G.add_edge(self._edge_sources[i], self._edge_targets[i], i)
        return G
