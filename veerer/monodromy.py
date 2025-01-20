r"""
Monodromy in linear subvarieties
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024 Vincent Delecroix
#                     2024 Kai Fu
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

from sage.graphs.digraph import DiGraph
from sage.groups.perm_gps.permgroup_named import SymmetricGroup

from .constants import RED, BLUE, HORIZONTAL, VERTICAL
from .permutation import perm_preimage, perm_orbit
from .veering_triangulation import VeeringTriangulation
from .labelled_digraph import LabelledDiGraph


# TODO: make this a proper morphism from the fundamental group of the labelled digraph
# to some permutation group of the separatrices
class SeparatrixMonodromy:
    r"""
    Monodromy of separatrices at a zero (or simple pole of quadratic differential) in a prime
    component.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from veerer.monodromy import SeparatrixMonodromy
        sage: vt = VeeringTriangulation("(0,8,~7)(~0,~6,7)(1,11,~10)(~1,~11,4)(2,10,~9)(~2,~4,5)(3,9,~8)(~3,~5,6)", "RRRRBBBBBBBB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: monodromy = SeparatrixMonodromy(ds_graph)
        sage: path = ds_graph.path(0)
        sage: path.random_append(10, reverse=False)
        sage: start = ds_graph.vertex_label(path.start())
        sage: end = ds_graph.vertex_label(path.end())
        sage: separatrices = start.vertex_separatrices()
        sage: separatrices_image = [monodromy.vertex_separatrix_transport(path, h, a) for (h, a) in separatrices]
        sage: separatrices_target = end.vertex_separatrices()
        sage: assert set(separatrices_image) == set(separatrices_target)
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
    def _rotate_vertex(state, half_edge, angle):
        # blue half-edge: nothing on angle, always fine
        # red half-edge: do -1 on angle, need to explore previous if angle=0
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
    def _rotate_vertex_back(state, half_edge, angle):
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
    def _rotate_face(state, half_edge, angle):
        if state._colouring[half_edge // 2] == RED:
            if angle == 0:
                half_edge = state.next_in_face(half_edge)
                num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                while num_seps == 1:
                    half_edge = state.next_in_face(half_edge)
                    num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                angle = num_seps - 2
            else:
                angle -= 1

        return (half_edge, angle)

    @staticmethod
    def _rotate_face_back(state, half_edge, angle):
        if state._colouring[half_edge // 2] == BLUE:
            angle += 1

        next_half_edge = state.previous_in_face(half_edge)
        if state._colouring[next_half_edge // 2] == BLUE:
            num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
            if num_seps == angle:
                half_edge = next_half_edge
                num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                while num_seps == 1:
                    half_edge = state.previous_in_face(half_edge)
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

    @staticmethod
    def _infinite_cylinder_strebel(mapping_back, half_edge):
        half_edge = next(k for k, h in enumerate(mapping_back) if h == half_edge)
        return half_edge

    @staticmethod
    def _infinite_cylinder_strebel_back(mapping_back, half_edge):
        return mapping_back[half_edge]

    def vertex_separatrix_transport(self, path, half_edge, angle):
        r"""
        Transport the vertex separatrix ``(half_edge, angle)`` along ``path``.
        """
        if path._graph is not self._graph:
            raise ValueError("invalid path for vertex monodromy")

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
                    half_edge = perm_preimage(relabelling, half_edge)
                else:
                    for e in edges:
                        half_edge, angle = self._flip(source, e, new_col, half_edge, angle)
                    half_edge = relabelling[half_edge]

            elif kind == "rotate":
                relabelling = transition[1]
                if reverse:
                    half_edge, angle = self._rotate_vertex_back(source, half_edge, angle)
                    half_edge = perm_preimage(relabelling, half_edge)
                else:
                    half_edge, angle = self._rotate_vertex(source, half_edge, angle)
                    half_edge = relabelling[half_edge]

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

    def face_separatrix_transport(self, path, half_edge, angle):
        r"""
        Transport the face separatrix ``(half_edge, angle)`` along this path.
        """
        if path._graph is not self._graph:
            raise ValueError("invalid path for face monodromy")

        for i in path:
            source = self._graph.vertex_label(self._graph.edge_source(i))
            target = self._graph.vertex_label(self._graph.edge_target(i))
            transition = self._graph.edge_label(i)

            reverse = i < 0

            # too expensive!!
            source._check_face_separatrix(half_edge, angle)

            kind = transition[0]
            if kind == "flip":
                relabelling = transition[4]
                if reverse:
                    half_edge = perm_preimage(relabelling, half_edge)
                else:
                    half_edge = relabelling[half_edge]

            elif kind == "rotate":
                relabelling = transition[1]
                if reverse:
                    half_edge, angle = self._rotate_face_back(source, half_edge, angle)
                    half_edge = perm_preimage(relabelling, half_edge)
                else:
                    half_edge, angle = self._rotate_face(source, half_edge, angle)
                    half_edge = relabelling[half_edge]

            elif kind == "strebel":
                mapping = transition[1]
                if reverse:
                    # NOTE: for Strebel operation the argument is always the veering triangulation
                    half_edge, angle = source._normalization_face_separatrix(half_edge, angle)
                    half_edge, angle = self._strebel_back(target, mapping, half_edge, angle)
                else:
                    half_edge, angle = self._strebel(source, mapping, half_edge, angle)

            # too expensive!!
            target._check_face_separatrix(half_edge, angle)

        return self._graph.vertex_label(path.end())._normalization_face_separatrix(half_edge, angle)

    def infinite_cylinder_transport(self, path, half_edge):
        r"""
        TESTS::

            sage: from veerer import VeeringTriangulationLinearFamily
            sage: from veerer.monodromy import SeparatrixMonodromy
            sage: vt = VeeringTriangulationLinearFamily("(0:1,1:1,2:1)(~0:1,~1:1,~2:1)", "RRR", [(1, 0, 0), (0, 1, 0), (0, 0, 1)])
            sage: ds_graph = vt.delaunay_strebel_graph()
            sage: mono = SeparatrixMonodromy(ds_graph)
            sage: for i in range(ds_graph.num_edges()):
            ....:     p1 = ds_graph.path(ds_graph.edge_source(i), [i])
            ....:     p2 = ds_graph.path(ds_graph.edge_target(i), [-i-1])
            ....:     for path in [p1, p2]:
            ....:         source = ds_graph.vertex_label(path.start())
            ....:         target = ds_graph.vertex_label(path.end())
            ....:         for h1 in source.boundary_half_edges():
            ....:             h2 = mono.infinite_cylinder_transport(path, h1)
            ....:             assert target.face_angle(h2) == 0
        """
        if path._graph is not self._graph:
            raise ValueError("invalid path for infinite cylinder monodromy")

        for i in path:
            source = self._graph.vertex_label(self._graph.edge_source(i))
            target = self._graph.vertex_label(self._graph.edge_target(i))
            transition = self._graph.edge_label(i)

            reverse = i < 0

            # TODO: remove as too expensive!!
            assert source.face_angle(half_edge) == 0

            kind = transition[0]
            if kind == "flip" or kind == "rotate":
                relabelling = transition[4 if kind == "flip" else 1]
                if reverse:
                    half_edge = perm_preimage(relabelling, half_edge)
                else:
                    half_edge = relabelling[half_edge]

            elif kind == "strebel":
                mapping = transition[1]
                mapping_back = transition[2]
                if reverse:
                    half_edge = self._infinite_cylinder_strebel_back(mapping_back, half_edge)
                else:
                    half_edge = self._infinite_cylinder_strebel(mapping_back, half_edge)

            # TODO: remove as too expensive!!
            assert target.face_angle(half_edge) == 0

        return min(perm_orbit(self._graph.vertex_label(path.end())._fp, half_edge))


def monodromy(ds_graph):
    r"""
    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from veerer.monodromy import monodromy

    The case of H(1^2)::

        sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "BRBBRBBRBBRB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: G = monodromy(ds_graph)
        sage: G.cardinality()
        8
        sage: G.structure_description()
        'C4 x C2'

    The case of H(1^2, -1^2)::

        sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:1)(~4:1)", "BRRRBBRRRB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: G = monodromy(ds_graph)
        sage: G.cardinality()
        16
        sage: G.structure_description()
        'C4 x C2 x C2'

    The case of H(3^2, -3^2)::

        sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:2)(~4:2)", "BRRRBBRRRB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: G = monodromy(ds_graph)
        sage: G.cardinality()
        20
        sage: G.structure_description()
        'C10 x C2'
    """
    root = ds_graph.root()

    mon = SeparatrixMonodromy(ds_graph)

    vertex_separatrices = root.vertex_separatrices(flat=True)
    vertex_separatrix_index = {ha: i for i, ha in enumerate(vertex_separatrices)}
    nv = len(vertex_separatrices)

    face_separatrices = root.face_separatrices(flat=True)
    face_separatrix_index = {ha: nv + i for i, ha in enumerate(face_separatrices)}
    nf = len(face_separatrices)

    infinite_cylinders = [min(f) for f in root.boundary_faces() if root.face_angle(f[0]) == 0]
    infinite_cylinder_index = {h: nv + nf + i for i, h in enumerate(infinite_cylinders)}
    nc = len(infinite_cylinders)

    n = nv + nf + nc

    perms = set()
    for path in ds_graph.fundamental_group_basis():
        p_vert = [vertex_separatrix_index[mon.vertex_separatrix_transport(path, h, a)] for (h, a) in vertex_separatrices]
        p_face = [face_separatrix_index[mon.face_separatrix_transport(path, h, a)] for (h, a) in face_separatrices]
        p_cyl = [infinite_cylinder_index[mon.infinite_cylinder_transport(path, h)] for h in infinite_cylinders]
        perms.add(tuple(p_vert) + tuple(p_face) + tuple(p_cyl))

    S = SymmetricGroup(range(n))
    return S.subgroup([S(list(p)) for p in perms])
