r"""
Delaunay-Strebel graph (for prime components).
"""

from array import array

from sage.misc.cachefunc import cached_method
from sage.graphs.digraph import DiGraph
from sage.misc.prandom import randrange

from .permutation import perm_preimage, perm_orbit
from .constellation import Constellation
from .automaton import Automaton
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

    EXAMPLES::

        sage: from veerer import *

    Let us build a Delaunay-Strebel graph in H(3^2, -3^2)::

        sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:2)(~4:2)", "BRRRBBRRRB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: ds_graph
        DelaunayStrebelGraph(VeeringTriangulation("(0:1,1:1,2:1,3:1)(~0:1,~1:1,~2:1,~3:1)", "RRRB"))
        sage: print(ds_graph.info())
        Delaunay-Strebel graph of VeeringTriangulation("(0:1,1:1,2:1,3:1)(~0:1,~1:1,~2:1,~3:1)", "RRRB") made of
          446 veering Delaunay states
          1 Strebel states
          1200 flip transitions
          42 rotation transitions
          42 Strebel transitions

    The vertices and edges are indexed by integers (for efficiency purposes). In order to get
    access to the underlying geometric data, one needs to call the methods ``vertex_label``
    and ``edge_label``::

        sage: ds_graph.vertex_label(122)
        VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,7,~6)(~5,8,9)(~7,~8,~9)(0:2)(~4:2)", "RBBBRBRBRB")
        sage: ds_graph.edge_label(37)
        ('flip',
         [5],
         1,
         2,
         array('i', [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 11, 10, 14, 15, 16, 17, 18, 19]))

    Note that one can reconstruct the Delaunay-Strebel graph from its string representation::


        sage: eval(repr(ds_graph), {'DelaunayStrebelGraph': DelaunayStrebelGraph, 'VeeringTriangulation': VeeringTriangulation}) == ds_graph
        True
    """
    def __init__(self, ds_graph):
        if isinstance(ds_graph, Constellation):
            ds_graph = ds_graph.delaunay_strebel_automaton()._graph
        elif isinstance(ds_graph, Automaton):
            ds_graph = ds_graph._graph

        if isinstance(ds_graph, DiGraph):
            root = min(vt for vt in ds_graph if isinstance(vt, VeeringTriangulation))
            LabelledDiGraph.__init__(self, ds_graph, root)
        elif isinstance(ds_graph, LabelledDiGraph):
            LabelledDiGraph.__init__(self, ds_graph)

        # store both the spanning tree oriented "towards" the root and "from" the root
        self._spanning_tree_to, self._complementary_edges = self.spanning_tree()
        self._spanning_tree_from = [[] for _ in range(len(self))]
        for i in self._spanning_tree_to:
            if i is not None:
                self._spanning_tree_from[self.edge_target(i)].append(~i)

    def __hash__(self):
        return hash(self._vertices[0])

    def __eq__(self, other):
        if type(self) is not type(other):
            raise TypeError

        return self._vertices[0] == other._vertices[0]

    def __ne__(self, other):
        if type(self) is not type(other):
            raise TypeError

        return self._vertices[0] != other._vertices[0]

    def __lt__(self, other):
        if type(self) is not type(other):
            raise TypeError

        return self._vertices[0] < other._vertices[0]

    def __le__(self, other):
        if type(self) is not type(other):
            raise TypeError

        return self._vertices[0] <= other._vertices[0]

    def __gt__(self, other):
        if type(self) is not type(other):
            raise TypeError

        return self._vertices[0] > other._vertices[0]

    def __ge__(self, other):
        if type(self) is not type(other):
            raise TypeError

        return self._vertices[0] >= other._vertices[0]

    def num_veering_states(self):
        r"""
        Return the number of states that are veering triangulations.
        """
        return sum(isinstance(state, VeeringTriangulation) for state in self._vertices)

    def num_strebel_states(self):
        r"""
        Return the number of states that are Strebel graph.
        """
        return sum(isinstance(state, StrebelGraph) for state in self._vertices)

    def num_flip_transitions(self):
        r"""
        Return the number of transitions corresponding to a forward Delaunay flip.
        """
        return sum(label[0] == "flip" for label in self._edges)

    def num_rotation_transitions(self):
        r"""
        Return the number of transitions corresponding to a rotation.
        """
        return sum(label[0] == "rotate" for label in self._edges)

    def num_strebel_transitions(self):
        r"""
        Return the number of transitions corresponding to a veering
        triangulation to Strebel forgetful map.
        """
        return sum(label[0] == "strebel" for label in self._edges)

    def __str__(self):
        return "Delaunay-Strebel graph on {} vertices and {} edges".format(self.num_verts(), self.num_edges())

    def __repr__(self):
        return "DelaunayStrebelGraph({})".format(self.root())

    def info(self):
        s = ["Delaunay-Strebel graph of {} made of".format(self._vertices[0])]
        s.append("  {} veering Delaunay states".format(self.num_veering_states()))
        s.append("  {} Strebel states".format(self.num_strebel_states()))
        s.append("  {} flip transitions".format(self.num_flip_transitions()))
        s.append("  {} rotation transitions".format(self.num_rotation_transitions()))
        s.append("  {} Strebel transitions".format(self.num_strebel_transitions()))
        return "\n".join(s)

    def root(self):
        return self._vertices[0]

    # TODO: rename as framing_trivialization
    @cached_method
    def separatrix_trivialization(self):
        r"""
        Return a trivialization of singularity labelling and choice of separatrices along the spanning tree.
        """
        from .monodromy import SeparatrixMonodromy
        monodromy = SeparatrixMonodromy(self)

        vertex_separatrices = [None] * len(self)
        face_separatrices = [None] * len(self)
        infinite_cylinders = [None] * len(self)
        folded_half_edges = [None] * len(self)

        root = self._vertices[0]

        vertex_separatrices[0], face_separatrices[0], infinite_cylinders[0], folded_half_edges[0] = root.framing()

        todo = self._spanning_tree_from[0][:]
        while todo:
            i = todo.pop()
            u = self.edge_source(i)
            v = self.edge_target(i)

            assert vertex_separatrices[u] is not None
            assert face_separatrices[u] is not None
            assert infinite_cylinders[u] is not None
            assert folded_half_edges[u] is not None

            assert vertex_separatrices[v] is None
            assert face_separatrices[v] is None
            assert infinite_cylinders[v] is None
            assert folded_half_edges[v] is None

            # TODO: we might want to avoid building a path if we just do parallel transport
            # along a single edge
            edge = self.path(u, [i])

            vertex_separatrices[v] = [monodromy.vertex_separatrix_transport(edge, h, a) for h, a in vertex_separatrices[u]]
            face_separatrices[v] = [monodromy.face_separatrix_transport(edge, h, a) for h, a in face_separatrices[u]]
            infinite_cylinders[v] = [monodromy.infinite_cylinder_transport(edge, h) for h in infinite_cylinders[u]]
            folded_half_edges[v] = [monodromy.folded_half_edge_transport(edge, h) for h in folded_half_edges[u]]

            todo.extend(self._spanning_tree_from[v])

        return tuple(vertex_separatrices), tuple(face_separatrices), tuple(infinite_cylinders), tuple(folded_half_edges)

    def framing(self, v=0):
        r"""
        Return the framing of the root or the vertex ``v`` if provided as argument.
        """
        vertex_separatrices, face_separatrices, infinite_cylinders, folded_half_edges = self.separatrix_trivialization()
        return (vertex_separatrices[v], face_separatrices[v], infinite_cylinders[v], folded_half_edges[v])

    # TODO: remove
    def _ambient_framing_group_data(self):
        from .framing_group import runs
        root = self._vertices[0]
        vseps, fseps, cseps, fhedges = self.framing(0)

        vertex_angles_and_multiplicities = [root.vertex_angle(h) for h, a in vseps]
        vertex_angles = []
        vertex_multiplicities = []
        for a, m in runs(vertex_angles_and_multiplicities):
            vertex_angles.append(a)
            vertex_multiplicities.append(m)

        face_angles_and_multiplicities = [-root.face_angle(h) for h, a in fseps]
        face_angles = []
        face_multiplicities = []
        for a, m in runs(face_angles_and_multiplicities):
            face_angles.append(a)
            face_multiplicities.append(m)

        ncyls = len(cseps)
        nfhedges = len(fhedges)

        return (vertex_angles, vertex_multiplicities, face_angles, face_multiplicities, ncyls, nfhedges)

    # TODO: remove
    def _ambient_framing_group(self):
        r"""
        Return the ambient framing group.

        The framing group is the group of permutation of singularities and
        separatrices. Any such permutation should respect the degree of
        singularties and the cyclic ordering of separatrices.
        """
        return self.root().framing_group()

    # TODO: remove
    def framing_group_element_permutation(self, g, v=0):
        state = self._vertices[v]
        return state.framing_group_element_permutation(g, self.framing(v))

    def automorphism_framing_monodromy(self, aut, v=0, monodromy=None, ambient_framing_group=None):
        if monodromy is None:
            from .monodromy import SeparatrixMonodromy
            monodromy = SeparatrixMonodromy(self)
        if ambient_framing_group is None:
            ambient_framing_group = self._ambient_framing_group()

        state = self._vertices[v]
        vseps0, fseps0, cseps0, fhedges0 = self.framing(v)
        vseps1 = [(aut[h], a) for h, a in vseps0]
        fseps1 = [(aut[h], a) for h, a in fseps0]
        cseps1 = [min(perm_orbit(state._fp, aut[h])) for h in cseps0]
        fhedges1 = [aut[h] for h in fhedges0]

        return self.root().framing_group_element((vseps1, fseps1, cseps1, fhedges1),
                                                       original_framing=(vseps0, fseps0, cseps0, fhedges0),
                                                       ambient_framing_group=ambient_framing_group)

    # TODO: rename path_framing_monodromy
    def framing_monodromy(self, path, monodromy=None, ambient_framing_group=None):
        r"""
        Return the framing monodromy of a (not necessarily closed) path.

        EXAMPLES::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:1)(~4:1)", "BRRRBBRRRB")
            sage: ds_graph = vt.delaunay_strebel_graph()  # long time
            sage: tree, complementary_edges = ds_graph.spanning_tree()  # long time

        The monodromy is trivial along the spanning tree::

            sage: for i in tree:  # long time
            ....:     if i is None:
            ....:         continue
            ....:     path = ds_graph.path(ds_graph.edge_source(i), [i])
            ....:     assert ds_graph.framing_monodromy(path).is_one()
            ....:     assert ds_graph.framing_monodromy(~path).is_one()

        And for complementary edges, it coincides with the canonical loop taken along the spanning tree::

            sage: for i in complementary_edges:  # long time
            ....:     path0 = ds_graph.path(ds_graph.edge_source(i), [i])
            ....:     g0 = ds_graph.framing_monodromy(path0)
            ....:     path1 = ds_graph.path(ds_graph.edge_target(i), [-i-1])
            ....:     g1 = ~ds_graph.framing_monodromy(path1)
            ....:     assert g0 == g1, (path0, path1, g0, g1, g0._p, g0._r, g1._p, g1._r)
            ....:     path2 = ds_graph.path(ds_graph.edge_source(i), [i])
            ....:     v = ds_graph.edge_source(i)
            ....:     while v != 0:
            ....:         i = tree[v]
            ....:         path2.appendleft(-i - 1)
            ....:         v = ds_graph.edge_target(i)
            ....:     v = ds_graph.edge_target(i)
            ....:     while v != 0:
            ....:         i = tree[v]
            ....:         path2.append(i)
            ....:         v = ds_graph.edge_target(i)
            ....:     g2 = ds_graph.framing_monodromy(path2)
            ....:     assert g0 == g2, (path0, path2, g0, g2, g0._p, g0._r, g2._p, g2._r)
        """
        if path._graph is not self:
            raise ValueError

        if monodromy is None:
            from .monodromy import SeparatrixMonodromy
            monodromy = SeparatrixMonodromy(self)
        if ambient_framing_group is None:
            ambient_framing_group = self._ambient_framing_group()

        u = path.start()
        v = path.end()

        vseps0, fseps0, cseps0, fhedges0 = self.framing(v)
        vseps1, fseps1, cseps1, fhedges1 = self.framing(u)

        vseps1 = [monodromy.vertex_separatrix_transport(path, h, a) for h, a in vseps1]
        fseps1 = [monodromy.face_separatrix_transport(path, h, a) for h, a in fseps1]
        cseps1 = [monodromy.infinite_cylinder_transport(path, h) for h in cseps1]
        fhedges1 = [monodromy.folded_half_edge_transport(path, h) for h in fhedges1]

        return self._vertices[v].framing_group_element((vseps1, fseps1, cseps1, fhedges1),
                                                       original_framing=(vseps0, fseps0, cseps0, fhedges0),
                                                       ambient_framing_group=ambient_framing_group)

    @cached_method
    def framing_group(self):
        r"""
        Return the monodromy of framing obtained by parallel transport along
        this Delaunay-Strebel graph.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamilies

        The case of H(1^2)::

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "BRBBRBBRBBRB")
            sage: ds_graph = vt.delaunay_strebel_graph()  # long time
            sage: G = ds_graph.framing_group()  # long time
            sage: G.cardinality()  # long time
            8
            sage: G.structure_description()  # long time
            'C4 x C2'

        The case of H(1^2, -1^2)::

            sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:1)(~4:1)", "BRRRBBRRRB")
            sage: ds_graph = vt.delaunay_strebel_graph()  # long time
            sage: G = ds_graph.framing_group()  # long time
            sage: G.cardinality()  # long time
            16
            sage: G.structure_description()  # long time
            'C4 x C2 x C2'

        The case of H(3^2, -3^2)::

            sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:2)(~4:2)", "BRRRBBRRRB")
            sage: ds_graph = vt.delaunay_strebel_graph()  # long time
            sage: G = ds_graph.framing_group()  # long time
            sage: G.cardinality()  # long time
            20
            sage: G.structure_description()  # long time
            'C10 x C2'

        In the following examples, we consider the permutation of Weierstrass points
        induced by the monodromy along Teichm\"uller curves in Q(1, -1^5) studied
        in [GuPa24]. The monodromy, only depends on the congruence modulo 8 of the
        discriminant::

            sage: for D, spin in [(5, None), (8, None), (9, None), (12, None), (13, None), (16, None), (17, 0), (17, 1)]:  # long time
            ....:     args = next(VeeringTriangulationLinearFamilies.H2_prototype_parameters(D, spin))
            ....:     f = VeeringTriangulationLinearFamilies.prototype_H2(*args)
            ....:     ds_graph = f.delaunay_strebel_graph()
            ....:     print("D={:2}  D%8={} {}".format(D, D % 8, ds_graph.framing_group().structure_description()))
            D= 5  D%8=5 C3 x D5
            D= 8  D%8=0 C3 x D4
            D= 9  D%8=1 C6 x S3
            D=12  D%8=4 C3 x D4
            D=13  D%8=5 C3 x D5
            D=16  D%8=0 C3 x D4
            D=17  D%8=1 C6 x S3
            D=17  D%8=1 C6 x S3

        The diagonal in H(0) x H(0) x H(0)::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)(6,7,8)(~6,~7,~8)", "RRBRRBRRB")
            sage: f = VeeringTriangulationLinearFamily(vt, [[1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 1, 0, 1, 1]])
            sage: f.delaunay_strebel_graph().framing_group().structure_description()
            'C2 x S4'
        """
        from .monodromy import SeparatrixMonodromy

        vseps, fseps, cseps, fhedges = self.separatrix_trivialization()

        G = self._ambient_framing_group()
        H = G.subgroup(mutable=True)
        monodromy = SeparatrixMonodromy(self)

        H.add_generator(G.rotation())

        for edge in self._complementary_edges:
            u = self.edge_source(edge)
            v = self.edge_target(edge)
            path = self.path(u, [edge])
            g = self.framing_monodromy(path, monodromy, G)
            H.add_generator(g)

        # NOTE: when the underlying differential lies on a disconnected surface with isomorphic
        # components, we need to include the permutation of the components
        # TODO: only use generators of the automorphism group
        v = 0
        root = self._vertices[0]
        for aut in root.automorphisms():
            vseps0 = vseps[0]
            vseps1 = [(aut[h], a) for h, a in vseps[0]]

            fseps0 = fseps[0]
            fseps1 = [root._normalize_face_separatrix(aut[h], a) for h, a in fseps[0]]

            cseps0 = cseps[0]
            cseps1 = [min(perm_orbit(root._fp, aut[h])) for h in cseps[0]]

            fhedges0 = fhedges[0]
            fhedges1 = [aut[h] for h in fhedges[0]]

            framing0 = (vseps0, fseps0, cseps0, fhedges0)
            framing1 = (vseps1, fseps1, cseps1, fhedges1)
            g = self._vertices[v].framing_group_element(framing1, original_framing=framing0, ambient_framing_group=G)
            H.add_generator(g)

        H.set_immutable()
        return H

#     # TODO:
#     # The following is clearly not the optimal strategy. We could have a self-loop
#     # that commutes with many other flips. We could delete all such loops but one
#     # and still generate.
#     # For a self-loop with flip "e" one can look at the connected component of the
#     # graph where "e" is not flipped and remove all but one "e loop".
#     def commuting_loops_and_squares(self, v):
#         r"""
#         Return loops and squares at ``v``.
#
#         EXAMPLES::
#
#             sage: from veerer import VeeringTriangulation
#             sage: vt = VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,8,~7)(~1,~8,3)(2,7,~6)(~2,~3,4)", "RRRBBBBBB")
#         """
#         distance2 = {}
#         for i0 in self.outgoing_edges(v, reverse=False):
#             label0 = self._edge_labels[i0]
#             if label0[0] != "flip":
#                 continue
#             edges0 = tuple(label0[1])
#             col0 = label0[3]
#             relabel = label0[4]
#             v1 = self._edge_targets[i0]
#             for i1 in self.outgoing_edges(v1, reverse=False):
#                 label1 = self._edge_labels[i1]
#                 if label1[0] != "flip":
#                     continue
#                 edges1 = tuple(sorted(perm_preimage(relabel, 2 * e) // 2 for e in label1[1]))
#                 col1 = label1[3]
#                 distance2[(edges0, col0, edges1, col1)] = (i0, i1)
#
#         loops = []
#         squares = []
#         for (edges0, col0, edges1, col1), (i0, i1) in distance2.items():
#             key = distance2.get((edges1, col1, edges0, col0))
#             if key is None:
#                 continue
#             j0, j1 = key
#             assert i0 != j0 and i1 != j1
#             if i0 == j1:
#                 loops.append((j0, j1, i1))
#             elif i0 < j0:
#                 squares.append((i0, i1, j0, j1))
#
#         return (loops, squares)
#
#     def reduced(self):
#         r"""
#         Return a graph whose fundamental group also generates the fundamental
#         group of the underlying stratum.
#         """
#         kept = [True] * self.num_edges()
#         for v in range(self.num_verts()):
#             loops, squares = self.commuting_loops_and_squares(v)
#             for (i, _, j) in loops:
#                 if kept[i] and kept[j]:
#                     r = randrange(2)
#                     if r == 0:
#                         kept[i] = False
#                     else:
#                         kept[j] = False
#
#             for (i0, i1, j0, j1) in squares:
#                 if kept[i0] and kept[i1] and kept[j0] and kept[j1]:
#                     r = randrange(4)
#                     if r == 0:
#                         kept[i0] = False
#                     elif r == 1:
#                         kept[i1] = False
#                     elif r == 2:
#                         kept[j0] = False
#                     else:
#                         kept[j1] = False
#
#         G = DiGraph(self.num_verts(), loops=self._digraph.allows_loops(), multiedges=self._digraph.allows_multiple_edges())
#         for i, b in enumerate(kept):
#             if b:
#                 G.add_edge(self._edge_sources[i], self._edge_targets[i], i)
#         return G


# # the only useful thing
# class MultiscaleDelaunayStrebelGraph:
#     r"""
#     A product of Delaunay-Strebel graphs endowed with a level structure.
#
#     TESTS::
#
#         sage: from veerer import *
#         sage: vt0 = VeeringTriangulation("(0,2,~1)(~0,~2,1)", "RBB")
#         sage: vt1 = VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRBB")
#         sage: vt2 = VeeringTriangulation("(0,1,2)(~2:2,~1:1,~0:1)", "BRB")
#         sage: m = MultiscaleDelaunayStrebelGraph([{vt0: 1, vt1: 2}, {vt0: 2, vt2: 1}])
#         sage: m
#         MultiscaleDelaunayStrebelGraph({
#           {DelaunayStrebelGraph(VeeringTriangulation("(0:1,1:1,2:1,3:1)(~0:1,~1:1,~2:1,~3:1)", "RRRB")): 1, DelaunayStrebelGraph(VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRRB")): 2},
#           {DelaunayStrebelGraph(VeeringTriangulation("(0:1,1:1,2:1,3:1)(~0:1,~1:1,~2:1,~3:1)", "RRRB")): 1}
#         })
#
#     The list of Delaunay-Strebel graphs at a given level is accessed using square brackets
#     as follows::
#
#         sage: m[0]
#         [DelaunayStrebelGraph(VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")),
#          DelaunayStrebelGraph(VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRRB")),
#          DelaunayStrebelGraph(VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRRB"))]
#         sage: m[1]
#         [DelaunayStrebelGraph(VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")),
#          DelaunayStrebelGraph(VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")),
#          DelaunayStrebelGraph(VeeringTriangulation("(0:1,~0:2,1:1,~1:2)", "RR"))]
#     """
#     def __init__(self, ds_graphs, check=True):
#         if not ds_graphs:
#             raise ValueError("empty input")
#
#     def __repr__(self):
#         return "MultiscaleDelaunayStrebelGraph({\n  " + ",\n  ".join(map(str, self._levels)) + "\n})"
#
#     def __len__(self):
#         r"""
#         EXAMPLES::
#
#             sage: from veerer import *
#             sage: vt0 = VeeringTriangulation("(0,2,~1)(~0,~2,1)", "RBB")
#             sage: vt1 = VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRBB")
#             sage: vt2 = VeeringTriangulation("(0,1,2)(~2:2,~1:1,~0:1)", "BRB")
#             sage: len(MultiscaleDelaunayStrebelGraph([{vt0: 1}]))
#             1
#             sage: len(MultiscaleDelaunayStrebelGraph([{vt0: 1}, {vt0: 2}]))
#             2
#         """
#         return len(self._levels)
#
#     def __getitem__(self, level):
#         try:
#             level = level.__index__()
#         except AttributeError:
#             raise TypeError("MultiscaleDelaunayStrebelGraph indices must be integers, not {}".format(type(i)))
#         return sum(([ds_graph] * multiplicity for ds_graph, multiplicity in self._levels[level].items()), [])
#
#     def __hash__(self):
#         raise NotImplementedError
#
#     def __eq__(self, other):
#         r"""
#         TESTS::
#
#             sage: from veerer import *
#             sage: vt0 = VeeringTriangulation("(0,2,~1)(~0,~2,1)", "RBB")
#             sage: vt1 = VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRBB")
#             sage: vt2 = VeeringTriangulation("(0,1,2)(~2:2,~1:1,~0:1)", "BRB")
#             sage: m0 = MultiscaleDelaunayStrebelGraph([{vt0: 1}]))
#             sage: m1  = MultiscaleDelaunayStrebelGraph([{vt0: 1}]))
#             sage: m2 = MultiscaleDelaunayStrebelGraph([{vt0: 2}]))
#             sage: m3 = MultiscaleDelaunayStrebelGraph([{vt1: 1}]))
#             sage: m4 = MultiscaleDelaunayStrebelGraph([{vt0: 1}, {vt0: 1}]))
#             sage: assert m0 == m1
#             sage: assert not (m0 == m2) and not (m0 == m3) and not (m3 == m4)
#             sage: assert not (m2 == m3) and not (m2 == m4)
#             sage: assert not (m3 == m4)
#         """
#         if type(self) is not type(other):
#             raise TypeError
#         return self._levels == other._levels
#
#     def __ne__(self, other):
#         r"""
#         TESTS::
#
#             sage: from veerer import *
#             sage: vt0 = VeeringTriangulation("(0,2,~1)(~0,~2,1)", "RBB")
#             sage: vt1 = VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRBB")
#             sage: vt2 = VeeringTriangulation("(0,1,2)(~2:2,~1:1,~0:1)", "BRB")
#             sage: m0 = MultiscaleDelaunayStrebelGraph([{vt0: 1}]))
#             sage: m1  = MultiscaleDelaunayStrebelGraph([{vt0: 1}]))
#             sage: m2 = MultiscaleDelaunayStrebelGraph([{vt0: 2}]))
#             sage: m3 = MultiscaleDelaunayStrebelGraph([{vt1: 1}]))
#             sage: m4 = MultiscaleDelaunayStrebelGraph([{vt0: 1}, {vt0: 1}]))
#             sage: assert not (m0 != m1)
#             sage: assert m0 != m2 and m0 != m3 and m3 != m4
#             sage: assert m2 != m3 and m2 != m4
#             sage: assert m3 != m4
#         """
#         if type(self) is not type(other):
#             raise TypeError
#         return self._levels != other._levels
#
#     def _cmp_(self, other):
#         if type(self) is not type(other):
#             raise TypeError("can not compare {} with {}".format(type(self).__name__, type(other).__name__))
#
#         data0 = len(self._levels)
#         data1 = len(other._levels)
#         c = (data0 > data1) - (data0 < data1)
#         if c:
#             return c
#
#         data0 = sorted(level.items() for level in self._levels)
#         data1 = sorted(level.items() for level in other._levels)
#         c = (data0 > data1) - (data0 < data1)
#         return c
#
#     def _richcmp_(self, other, op):
#         if type(self) is not type(other):
#             raise TypeError("can not compare {} with {}".format(type(self).__name__, type(other).__name__))
#
#         return rich_to_bool(op, self._cmp_(other))
#
#     def __lt__(self, other):
#         return self._richcmp_(other, op_LT)
#
#     def __le__(self, other):
#         return self._richcmp_(other, op_LE)
#
#     def __gt__(self, other):
#         return self._richcmp_(other, op_GT)
#
#     def __ge__(self, other):
#         return self._richcmp_(other, op_GE)
#
#     def _check_level(self, level):
#         if not isinstance(level, numbers.Integral):
#             raise TypeError("level must be integral")
#         level = int(level)
#         if level < 0:
#             level = -level
#         if not 0 <= level < len(self._levels):
#             raise ValueError("level out of range")
#         return level
#
#     def _ambient_framing_group_data(self, level):
#         r"""
#         EXAMPLES::
#
#             sage: from veerer import *
#             sage: vt0 = VeeringTriangulation("(0,2,~1)(~0,~2,1)", "RBB")
#             sage: vt1 = VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRBB")
#             sage: vt2 = VeeringTriangulation("(0,1,2)(~2:2,~1:1,~0:1)", "BRB")
#             sage: MultiscaleDelaunayStrebelGraph([{vt0: 2, vt1: 1}, {vt2: 3}])._ambient_framing_group()
#             (FramingGroup(2^2, 2^2, 1^2, 2^9, 2^3), [[0, 2], [6]])
#         """
#         from .framing_group import FramingGroup
#
#         vertex_angles = []
#         vertex_multiplicities = []
#         face_angles = []
#         face_multiplicities = []
#         ncyls = nfedges = 0
#         ds_graphs = self._levels[level]
#         for comp, (ds_graph, multiplicity) in enumerate(ds_graphs.items()):
#             local_vertex_angles, local_vertex_multiplicities, local_face_angles, local_face_multiplicities, local_ncyls, local_nfedges = ds_graph._ambient_framing_group_data()
#
#             vertex_angles.extend(local_vertex_angles)
#             vertex_multiplicities.extend(x * multiplicity for x in local_vertex_multiplicities)
#
#             face_angles.extend(local_face_angles)
#             face_multiplicities.extend(x * multiplicity for x in local_face_multiplicities)
#
#             ncyls += local_ncyls * multiplicity
#             nfedges += local_nfedges * multiplicity
#
#         return (vertex_angles, vertex_multiplicities, face_angles, face_multiplicities, ncyls, nfedges)
#
#     def _ambient_framing_group(self, level):
#         r"""
#         Return the ambient framing group.
#
#         The framing group is the group of permutation of singularities and
#         separatrices. Any such permutation should respect the degree of
#         singularties and the cyclic ordering of separatrices.
#         """
#         from .framing_group import FramingGroup
#         vertex_angles, vertex_multiplicities, face_angles, face_multiplicities, ncyls, nfedges = self._ambient_framing_group_data(level)
#         angles = vertex_angles + face_angles
#         multiplicities = vertex_multiplicities + face_multiplicities
#         if ncyls:
#             angles.append(1)
#             multiplicities.append(ncyls)
#         if nfedges:
#             angles.append(1)
#             multiplicities.append(nfedges)
#
#         return FramingGroup(angles, multiplicities)
#
#     def framing_group_element_permutation(self, level, g, v=None):
#         level = self._check_level(level)
#
#         if v is None:
#             v = [0] * len(self[level])
#
#         all_seps = []
#         nv = []
#         nf = []
#         nc = []
#         nfc = []
#         ds_graphs = self[levels]
#         for comp, ds_graph in enumerate(self[level]):
#             local_v = v[level][comp]
#             local_state = ds_graph._vertices[local_v]
#             vseps, fseps, cseps, fedges = ds_graph.separatrix_trivialization()
#
#             # vertex separatrices at (level, comp)
#             for h, a in vseps[local_v]:
#                 orbit = [(level, comp, h, b) for b in range(a, local_state.half_edge_num_separatrices(h, check=False))]
#                 for hh in perm_orbit(local_state._vp, h)[1:]:
#                     orbit.extend((level, comp, hh, b) for b in range(state.half_edge_num_separatrices(hh, check=False)))
#                 orbit.extend((level, comp, h, b) for b in range(a))
#                 all_seps.append(orbit)
#
#             # face separatrices at (level, comp)
#             for h, a in fseps[local_v]:
#                 orbit = [(level, comp, h, b) for b in range(a, -1, -1)]
#                 for hh in perm_orbit(local_state._fp, h)[1:]:
#                     orbit.extend((level, comp, hh, b) for b in range(local_state.half_edge_num_separatrices(hh, check=False) -2, -1, -1))
#                 orbit.extend((level, comp, h, b) for b in range(state.half_edge_num_separatrices(h, check=False) - 2, a, -1))
#
#             # infinite cylinders
#             all_seps.extend((level, comp, h) for h in cseps[local_v])
#
#             # folded edges
#             all_seps.extend((level, comp, h) for h in fedges[local_v])
#
#
#     # TODO
#     @cached_method
#     def framing_group(self):
#         r"""
#         Return the monodromy of framing obtained by parallel transport in each
#         prime component and exchange of isomorphic components in the same
#         level.
#         """
#         G = self._ambient_framing_group()
#         H = G.subgroup(mutable=True)
#
#         # TODO: use multiplicities
#         # add generators for monodromies in each component
#         for level, ds_graphs in enumerate(self._levels):
#             for comp, ds_graph in enumerate(ds_graphs):
#                 Gloc = ds_graph.framing_group()
#
#         # add generator for exchange of isomorphic components in a given level
#
#         H.set_immutable()
#         return H
#
#     def framing_group_element_permutation(self, g, v=None):
#         r"""
#         Given an element of the framing group ``g`` return a quadruple of
#         dictionaries ``(d_vseps, d_fseps, d_cseps, d_fedges)`` encoding
#         permutations of vertex separatrices, face separatrices, infinite
#         cylinders and folded edges.
#
#         The keys and values
#         - for ``d_vseps`` are quadruples ``(level, component, half_edge, angle)``
#         - for ``d_fseps`` are quadruples ``(level, component, half_edge, angle)``
#         - for ``d_cseps`` are triples ``(level, component, half_edge)``
#         - for ``d_fedges`` are triples ``(level, component, half_edge)
#
#         The argument ``v`` is an optional vertex
#
#         EXAMPLES::
#
#             sage: from veerer import VeeringTriangulation
#             sage: vt = VeeringTriangulation("(0:4,~0:2)","R")
#             sage: ds_graph = vt.delaunay_strebel_graph()
#             sage: G = ds_graph.ambient_framing_group()
#             sage: G.rotation()
#         """
#         raise NotImplementedError
