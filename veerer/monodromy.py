from sage.graphs.digraph import DiGraph
from sage.groups.perm_gps.permgroup_named import SymmetricGroup

from .constants import RED, BLUE, HORIZONTAL, VERTICAL
from .permutation import perm_preimage
from .veering_triangulation import VeeringTriangulation
from .labelled_digraph import LabelledDiGraph


# TODO: make this a proper morphism from the fundamental group of the labelled digraph
# to some permutation group of the separatrices
class VertexSeparatrixMonodromy:
    r"""
    Monodromy of separatrices at a zero (or simple pole of quadratic differential) in a prime
    component.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from surface_dynamics import Stratum
        sage: from veerer.delaunay_strebel_path import DelaunayStrebelPath
        sage: DS = VeeringTriangulation.from_stratum(Stratum([1, 1])).delaunay_strebel_graph()
        sage: start = next(iter(DS))
        sage: path = DelaunayStrebelPath(DS, start)
        sage: path.random_append(10, reverse=False)
        sage: separatrices = [(h, 0) for h in path.start().right_wedges()]
        sage: separatrices_image = [path.vertex_separatrix_transport(h, a) for (h, a) in separatrices]
        sage: separatrices_target = [(h, 0) for h in path.end().right_wedges()]
        sage: assert set(separatrices_image) == set(separatrices_target), (separatrices, separatrices_image, separatrices_target)
    """
    def __init__(self, graph):
        self._graph = graph

    @staticmethod
    def _relabelling(relabelling, half_edge, angle):
        return (relabelling[half_edge], angle)

    @staticmethod
    def _relabelling_back(relabelling, half_edge, angle):
        return (perm_preimage(relabelling, half_edge), angle)

    # Transport of vertex separatrices (separatrices of a zero of a simple pole of a quadratic differential)

    @staticmethod
    def _flip(state, e, col, half_edge, angle):
        assert half_edge != 2 * e and half_edge != (2 * e + 1)
        a, b, c, d = state.square_about_half_edge(2 * e, check=False)
        if half_edge == b:
            assert angle == 0
            return (2 * e + 1, 0) if col == RED else (half_edge, angle)
        elif half_edge == d:
            assert angle == 0
            return (2 * e, 0) if col == RED else (half_edge, angle)

        return (half_edge, angle)

    @staticmethod
    def _flip_back(state, e, col, half_edge, angle):
        if half_edge == 2 * e:
            assert state._colouring[e] == RED
            assert angle == 0
            a, b, c, d = state.square_about_half_edge(2 * e, check=False)
            return (c, 0)
        elif half_edge == 2 * e + 1:
            assert state._colouring[e] == RED
            assert angle == 0
            a, b, c, d = state.square_about_half_edge(2 * e, check=False)
            return (a, 0)

        return (half_edge, angle)

    @staticmethod
    def _rotate(state, half_edge, angle):
        # blue half-edge: nothing on angle, always fine
        # red half-edge: do -1 on angle, need to explore previous if angle=0
        next_half_edge = state.next_at_vertex(half_edge)
        if state._colouring[half_edge // 2] == RED:
            if angle == 0:
                half_edge = state.previous_at_vertex(half_edge)
                num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                while num_seps == 0:
                    half_edge = state.previous_at_vertex(half_edge)
                    num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                angle = num_seps - 1
            else:
                angle -= 1

        return (half_edge, angle)

    @staticmethod
    def _rotate_back(state, half_edge, angle):
        # blue half-edge: +1 on angle, if next half-edge is blue and angle=max need to explore next
        # red half-edge: nothing on angle, if next half-edge is blue and angle=max need to explore next
        if state._colouring[half_edge // 2] == BLUE:
            angle += 1

        next_half_edge = state.next_at_vertex(half_edge)
        if state._colouring[next_half_edge // 2] == BLUE:
            num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
            if num_seps == angle:
                half_edge = next_half_edge
                num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                while num_seps == 0:
                    half_edge = state.next_at_vertex(half_edge)
                    num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                angle = 0

        return (half_edge, angle)

    @staticmethod
    def _strebel(state, mapping, half_edge, angle):
        while mapping[half_edge] == -1:
            half_edge = state.previous_at_vertex(half_edge)
            angle += state._bdry[half_edge] + (state._colouring[half_edge // 2] == RED and state._colouring[state._vp[half_edge] // 2] == BLUE)
        return (mapping[half_edge], angle)

    @staticmethod
    def _strebel_back(state, mapping, half_edge, angle):
        half_edge = next(h for h in range(len(mapping)) if mapping[h] == half_edge)
        num_seps = state._bdry[half_edge] + (state._colouring[half_edge // 2] == RED and state._colouring[state._vp[half_edge] // 2] == BLUE)
        while angle >= num_seps:
            angle -= num_seps
            half_edge = state.next_at_vertex(half_edge)
            num_seps = state._bdry[half_edge] + (state._colouring[half_edge // 2] == RED and state._colouring[state._vp[half_edge] // 2] == BLUE)

        return (half_edge, angle)

    def __call__(self, path, x):
        r"""
        Transport the vertex separatrix ``(half_edge, angle)`` along ``path``.
        """
        if path._graph is not self._graph:
            raise ValueError("invalid path for vertex monodromy")

        half_edge, angle = x

        for i in path:
            source = self._graph.vertex_label(self._graph.edge_source(i))
            target = self._graph.vertex_label(self._graph.edge_target(i))
            transition = self._graph.edge_label(i)

            reverse = i < 0

            # too expensive!!
            # source._check_vertex_separatrix(half_edge, angle)

            kind = transition[0]
            if kind == "flip":
                edges = transition[1]
                old_col = transition[2]
                new_col = transition[3]
                relabelling = transition[4]
                if reverse:
                    for e in edges:
                        half_edge, angle = self._flip_back(source, relabelling[2 * e] // 2, old_col, half_edge, angle)
                    half_edge, angle = self._relabelling_back(relabelling, half_edge, angle)
                else:
                    for e in edges:
                        half_edge, angle = self._flip(source, e, new_col, half_edge, angle)
                    half_edge, angle = self._relabelling(relabelling, half_edge, angle)

            elif kind == "rotate":
                relabelling = transition[1]
                if reverse:
                    half_edge, angle = self._rotate_back(source, half_edge, angle)
                    half_edge, angle = self._relabelling_back(relabelling, half_edge, angle)
                else:
                    half_edge, angle = self._rotate(source, half_edge, angle)
                    half_edge, angle = self._relabelling(relabelling, half_edge, angle)

            elif kind == "strebel":
                mapping = transition[1]
                if reverse:
                    # NOTE: for Strebel operation the argument is always the veering triangulation
                    half_edge, angle = self._strebel_back(target, mapping, half_edge, angle)
                else:
                    half_edge, angle = self._strebel(source, mapping, half_edge, angle)

            # too expensive!!
            # target._check_vertex_separatrix(half_edge, angle)

        return (half_edge, angle)


# TODO: there is nothing implemented yet
class FaceSeparatrixMonodromy:
    # Transport of face separatrices (separatrices of a higher order poles)

    @staticmethod
    def _rotate(state, half_edge, angle):
        raise NotImplementedError

    @staticmethod
    def _rotate_back(state, half_edge, angle):
        raise NotImplementedError

    @staticmethod
    def _strebel(state, mapping, half_edge, angle):
        raise NotImplementedError

    @staticmethod
    def _strebel_back(state, mapping, half_edge, angle):
        raise NotImplementedError

    def __call__(self, path, x):
        r"""
        Transport the face separatrix ``(half_edge, angle)`` along this path.
        """
        half_edge, angle = x

        for i in path:
            source = self._graph.vertex_label(self._graph.edge_source(i))
            target = self._graph.vertex_label(self._graph.edge_target(i))
            transition = self._graph.edge_label(i)

            reverse = i < 0

            # too expensive!!
            # source._check_face_separatrix(half_edge, angle)

            kind = transition[0]
            if kind == "flip":
                continue

            elif kind == "rotate":
                relabelling = transition[1]
                if reverse:
                    half_edge, angle = self._rotate_back(source, half_edge, angle)
                    half_edge, angle = self._relabelling_back(relabelling, half_edge, angle)
                else:
                    half_edge, angle = self._rotate(source, half_edge, angle)
                    half_edge, angle = self._relabelling(relabelling, half_edge, angle)

            elif kind == "strebel":
                mapping = transition[1]
                if reverse:
                    # NOTE: for Strebel operation the argument is always the veering triangulation
                    half_edge, angle = self._strebel_back(target, mapping, half_edge, angle)
                else:
                    half_edge, angle = self._strebel(source, mapping, half_edge, angle)

            # too expensive!!
            # target._check_face_separatrix(half_edge, angle)

        # TODO: canonicalize the output
        return (half_edge, angle)


# TODO: this function has to move closer to Delaunay-Strebel graphs and linear subvarieties
def vertex_separatrices_monodromy(ds_graph, root=None):
    r"""
    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from veerer.monodromy import vertex_separatrices_monodromy

    The case of H(1^2)::

        sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "BRBBRBBRBBRB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: G = vertex_separatrices_monodromy(ds_graph)
        sage: G.cardinality()
        8
        sage: G.structure_description()
        'C4 x C2'

    The case of H(1^2, -1^2)::

        sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:1)(~4:1)", "BRRRBBRRRB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: G = vertex_separatrices_monodromy(ds_graph)
        sage: G.cardinality()
        8
        sage: G.structure_description()
        'C4 x C2'
    """
    if root is None:
        root = next(state for state in ds_graph if isinstance(state, VeeringTriangulation))

    # TODO: the Delaunay-Strebel graph ought to be a LabelledDiGraph rather
    # than a sage DiGraph
    G = LabelledDiGraph(ds_graph)
    monodromy = VertexSeparatrixMonodromy(G)

    separatrix_vertex_angle = {}
    separatrix_index = {}
    separatrices = []
    i = 0
    for v, seps in enumerate(root.vertex_separatrices(flat=False)):
        for a, s in enumerate(seps):
            separatrix_vertex_angle[s] = (v, a)
            separatrix_index[s] = i
            separatrices.append(s)
            i += 1

    perms = set()
    for path in G.fundamental_group_basis():
        p = [separatrix_index[monodromy(path, (h, a))] for (h, a) in separatrices]
        perms.add(tuple(p))

    S = SymmetricGroup(range(len(separatrices)))
    return S.subgroup([S(list(p)) for p in perms])
