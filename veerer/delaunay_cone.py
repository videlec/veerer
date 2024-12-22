r"""
Delaunay cone of veering triangulations and veering triangulation families.
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024 Vincent Delecroix
#
#  veerer is free software: you can redistribute it and/or modify it under the
#  terms of the GNU General Public License version 3 as published by the Free
#  Software Foundation.
#
#  veerer is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with veerer. If not, see <https://www.gnu.org/licenses/>.
# ****************************************************************************

import collections
import itertools

from sage.misc.cachefunc import cached_method
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.matrix.constructor import matrix
from sage.modules.free_module import FreeModule
from sage.geometry.polyhedron.combinatorial_polyhedron.base import CombinatorialPolyhedron

from .constants import BLUE, RED, HORIZONTAL, VERTICAL
from .polyhedron.linear_algebra import vector_normalize
from .polyhedron.linear_expression import LinearExpressions, ConstraintSystem


class DelaunayCone:
    r"""
    The Delaunay cone of a veering triangulation.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily

        sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRBBBR")
        sage: vt.delaunay_cone()
        8-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRBBBR") made of
         2 forward-flip facets
         2 backward-flip facets
         5 x-degeneration facets
         4 y-degeneration facets

        sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~7,~5)(~3,~4,~2)(~6,~1,~8)", "RRBRRBRRB")
        sage: vt.delaunay_cone()
        8-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~7,~5)(~1,~8,~6)(~2,~3,~4)(3,4,5)(6,7,8)", "RRBRRBRRB") made of
         2 forward-flip facets
         3 backward-flip facets
         5 x-degeneration facets
         4 y-degeneration facets

        sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~1,~5)(~3,~7,~8)(~6,~4,~2)", "RRBRRBRBB")
        sage: vt.delaunay_cone()
        8-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~1,~5)(~2,~6,~4)(3,4,5)(~3,~7,~8)(6,7,8)", "RRBRRBRBB") made of
         3 forward-flip facets
         2 backward-flip facets
         4 x-degeneration facets
         4 y-degeneration facets
    """
    def __init__(self, vt, cone):
        self._vt = vt
        self._cone = cone
        self._V = FreeModule(vt.base_ring(), 2 * self._vt._ne)

    @cached_method
    def facets_kind_and_data(self):
        kinds = [None] * len(self.facets())
        datas = [[] for _ in range(len(self.facets()))]

        for face, edges in self.x_vanishing_facets():
            for i in face.ambient_H_indices():
                kinds[i] = 'x'
                datas[i] = edges
        for face, edges in self.y_vanishing_facets():
            for i in face.ambient_H_indices():
                kinds[i] = 'y'
                datas[i] = edges
        for face, edges in self.forward_delaunay_facets():
            for i in face.ambient_H_indices():
                kinds[i] = 'f'
                datas[i] = edges
        for face, edges in self.backward_delaunay_facets():
            for i in face.ambient_H_indices():
                kinds[i] = 'b'
                datas[i] = edges

        assert not any(v is None for v in kinds)
        return tuple(kinds), tuple(datas)

    @cached_method
    def rays(self):
        ans = list(map(self._V, self._cone.rays()))
        for r in ans:
            r.set_immutable()
        return ans

    def eqns(self):
        return self._cone.eqns()

    def space_dimension(self):
        return 2 * self._vt._ne

    @cached_method
    def facets(self):
        ans = list(map(self._V, self._cone.ieqs()))
        for f in ans:
            f.set_immutable()
        return ans

    ieqs = facets

    @cached_method
    def affine_dimension(self):
        return self._cone.affine_dimension()

    @cached_method
    def combinatorial_polyhedron(self):
        r"""
        Columns correspond to inequalities the rows correspond to rays.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: vt.delaunay_cone().combinatorial_polyhedron()
            A 3-dimensional combinatorial polyhedron with 6 facets
        """
        return CombinatorialPolyhedron(incidence_matrix(self.facets(), self.rays()))

    def x_vanishing_face(self, e):
        r"""
        Return the x-vanishing face of the edge ``e``.
        """
        CP = self.combinatorial_polyhedron()
        Vrep = [i for i, r in enumerate(self.rays()) if r[e] == 0]
        return CP.join_of_Vrep(*Vrep)

    def y_vanishing_face(self, e):
        r"""
        Return the y-vanishing face of the edge ``e``.
        """
        CP = self.combinatorial_polyhedron()
        ne = self._vt._ne
        Vrep = [i for i, r in enumerate(self.rays()) if r[ne + e] == 0]
        return CP.join_of_Vrep(*Vrep)

    def vanishing_face(self, e):
        r"""
        Return the vanishing face of the edge ``e``.
        """
        CP = self.combinatorial_polyhedron()
        return CP.meet_of_Hrep(*self.x_vanishing_face(e).ambient_H_indices(),
                               *self.y_vanishing_face(e).ambient_H_indices())

    def forward_delaunay_face(self, e, check=True):
        r"""
        Return the forward Delaunay face of the edge ``e``.

        The edge ``e`` must be a forward flippable edge.
        """
        # x[e] = y[a] + y[d]
        if check and not self._vt.is_forward_flippable(e):
            raise ValueError("non forward-flippable edge e={}".format(e))
        ne = self._vt._ne
        CP = self.combinatorial_polyhedron()
        a, b, c, d = self._vt.square_about_half_edge(2 * e)
        Vrep = [i for i, r in enumerate(self.rays()) if r[e] == r[ne + a//2] + r[ne + d//2]]
        return CP.join_of_Vrep(*Vrep)

    def backward_delaunay_face(self, e, check=True):
        r"""
        Return the backward Delaunay face of the edge ``e``.

        The edge ``e`` must be a backward flippable edge.
        """
        # y[e] = x[a] + x[d]
        if check and not self._vt.is_backward_flippable(e):
            raise ValueError("non backward-flippable edge e={}".format(e))
        ne = self._vt._ne
        CP = self.combinatorial_polyhedron()
        a, b, c, d = self._vt.square_about_half_edge(2 * e)
        Vrep = [i for i, r in enumerate(self.rays()) if r[ne + e] == r[a // 2] + r[d // 2]]
        return CP.join_of_Vrep(*Vrep)

    def _filter_facets(self, edges_and_faces):
        ans = collections.defaultdict(list)
        facets = {}
        for e, face in edges_and_faces:
            if face.dimension() == self.affine_dimension() - 2:
                Hrep = face.ambient_H_indices()
                ans[Hrep].append(e)
                facets[Hrep] = face
        return [(facets[Hrep], ans[Hrep]) for Hrep in facets]

    def x_vanishing_facets(self):
        return self._filter_facets((e, self.x_vanishing_face(e)) for e in range(self._vt._ne))

    def y_vanishing_facets(self):
        return self._filter_facets((e, self.y_vanishing_face(e)) for e in range(self._vt._ne))

    def forward_delaunay_facets(self):
        return self._filter_facets((e, self.forward_delaunay_face(e)) for e in self._vt.forward_flippable_edges())

    def backward_delaunay_facets(self):
        return self._filter_facets((e, self.backward_delaunay_face(e)) for e in self._vt.backward_flippable_edges())

    def __repr__(self):
        s = "{}-dimensional Delaunay cone of {} made of\n"
        s += " {} forward-flip facets\n"
        s += " {} backward-flip facets\n"
        s += " {} x-degeneration facets\n"
        s += " {} y-degeneration facets"
        return s.format(self.affine_dimension(), self._vt,
                        len(self.forward_delaunay_facets()),
                        len(self.backward_delaunay_facets()),
                        len(self.x_vanishing_facets()),
                        len(self.y_vanishing_facets()))


def incidence_matrix(facets, rays, mutable=False):
        ans = matrix(ZZ, len(rays), len(facets))
        for i, r in enumerate(rays):
            for j, f in enumerate(facets):
                ans[i, j] = r.dot_product(f).is_zero()
        if not mutable:
            ans.set_immutable()
        return ans
