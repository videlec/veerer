r"""
Delaunay and refined Delaunay cones of veering triangulations and veering triangulation families.
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024-2026 Vincent Delecroix
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
    The Delaunay cone or refined Delaunay cone of a veering triangulation.

    The cone is embedded in `R^{2 ne}` where `ne` is the number of edges of the
    underlying veering triangulation. The first ``ne`` coordinates indexed by
    ``0, 1, ..., ne-1`` are the horizontal or `x`-coordinates while the last
    ``ne`` coordinates index by ``ne, ne+1, ..., 2ne-1``.

    This class is usually not constructed via its constructor but via one of
    the functions
    - :meth:`~veerer.veering_triangulation.VeeringTriangulation.delaunay_cone`
    -  :meth:`~veerer.veering_triangulation.VeeringTriangulation.delaunay_cone`

    the :class:`~veerer.veering_triangulation.VeeringTriangulation` class.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily

        sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRBBBR")
        sage: C = vt.delaunay_cone()
        sage: C
        DelaunayCone(VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRBBBR"))
        sage: C.info()
        8-dimensional Delaunay cone made of
         2 forward-flip facets
         2 backward-flip facets
         5 x-degeneration facets
         4 y-degeneration facets

        sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~7,~5)(~3,~4,~2)(~6,~1,~8)", "RRBRRBRRB")
        sage: C = vt.delaunay_cone()
        sage: C
        DelaunayCone(VeeringTriangulation("(0,1,2)(~0,~7,~5)(~1,~8,~6)(~2,~3,~4)(3,4,5)(6,7,8)", "RRBRRBRRB"))
        sage: C.info()
        8-dimensional Delaunay cone made of
         2 forward-flip facets
         3 backward-flip facets
         5 x-degeneration facets
         4 y-degeneration facets

        sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~1,~5)(~3,~7,~8)(~6,~4,~2)", "RRBRRBRBB")
        sage: C = vt.delaunay_cone()
        sage: C
        DelaunayCone(VeeringTriangulation("(0,1,2)(~0,~1,~5)(~2,~6,~4)(3,4,5)(~3,~7,~8)(6,7,8)", "RRBRRBRBB"))
        sage: C.info()
        8-dimensional Delaunay cone made of
         3 forward-flip facets
         2 backward-flip facets
         4 x-degeneration facets
         4 y-degeneration facets
    """
    def __init__(self, vt, cone):
        r"""
        INPUT:

        - ``vt`` -- veering triangulation or veering triangulation family

        - ``cone`` -- a :class:`~veerer.polyhedron.cone.Cone`
        """
        self._vt = vt
        self._cone = cone
        self._V = FreeModule(vt.base_ring(), 2 * self._vt._ne)

    def __repr__(self):
        r"""
        TESTS::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: repr(vt.delaunay_cone())  # indirect doctest
            'DelaunayCone(VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB"))'
        """
        return "DelaunayCone({})".format(self._vt)

    def info(self):
        r"""
        TESTS::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: vt.delaunay_cone().info()
            4-dimensional Delaunay cone made of
             1 forward-flip facet
             1 backward-flip facet
             2 x-degeneration facets
             2 y-degeneration facets
        """
        nf = len(self.forward_delaunay_facets())
        nb = len(self.backward_delaunay_facets())
        nvx = len(self.x_vanishing_facets())
        nvy = len(self.y_vanishing_facets())
        nec = len(self.edge_critical_facets())
        ntc = len(self.triangle_critical_facets())
        s = [f"{self.affine_dimension()}-dimensional Delaunay cone made of"]
        if nf:
            s.append(" {} forward-flip facet{}".format(nf, "s" if nf >= 2 else ""))
        if nb:
            s.append(" {} backward-flip facet{}".format(nb, "s" if nb >= 2 else ""))
        if nvx:
            s.append(" {} x-degeneration facet{}".format(nvx, "s" if nvx >= 2 else ""))
        if nvy:
            s.append(" {} y-degeneration facet{}".format(nvy, "s" if nvy >= 2 else ""))
        if nec:
            s.append(" {} edge-critical facet{}".format(nec, "s" if nec >= 2 else ""))
        if ntc:
            s.append(" {} triangle-critical facet{}".format(ntc, "s" if ntc >= 2 else ""))

        print("\n".join(s))

    def space_dimension(self):
        r"""
        Return the ambient dimension of the cone which is twice the number of
        edges of the underlying veering triangulation.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: vt.delaunay_cone().space_dimension()
            6
        """
        return 2 * self._vt._ne

    @cached_method
    def rays(self):
        r"""
        Return the rays of this cone.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: vt.delaunay_cone().rays()
            ((1, 1, 0, 1, 1, 0),
             (2, 2, 0, 1, 0, 1),
             (1, 1, 0, 1, 0, 1),
             (0, 1, 1, 2, 0, 2),
             (0, 2, 2, 1, 0, 1),
             (0, 1, 1, 1, 1, 0),
             (0, 1, 1, 2, 2, 0))
        """
        ans = list(map(self._V, self._cone.rays()))
        for r in ans:
            r.set_immutable()
        return tuple(ans)

    def eqns(self):
        r"""
        Return a basis of equations for this cone.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: vt.delaunay_cone().eqns()
            ((0, 0, 0, 1, -1, -1), (1, -1, 1, 0, 0, 0))
        """
        ans = list(map(self._V, self._cone.eqns()))
        for r in ans:
            r.set_immutable()
        return tuple(ans)

    @cached_method
    def ieqs(self):
        r"""
        Return the inequations defining this cone.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: vt.delaunay_cone().ieqs()
            ((0, -1, 0, 2, -1, 0),
             (0, 0, 0, 1, -1, 0),
             (0, 0, 0, 0, 1, 0),
             (-1, 1, 0, 0, 0, 0),
             (1, 0, 0, 0, 0, 0),
             (-1, 2, 0, -1, 0, 0))
        """
        ans = list(map(self._V, self._cone.ieqs()))
        for f in ans:
            f.set_immutable()
        return tuple(ans)

    facets = ieqs

    @cached_method
    def affine_dimension(self):
        r"""
        Return the affine dimension of this cone.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: vt.delaunay_cone().affine_dimension()
            4
        """
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

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.x_vanishing_face(0)
            A 2-dimensional face of a 3-dimensional combinatorial polyhedron
            sage: C.x_vanishing_face(1)
            A -1-dimensional face of a 3-dimensional combinatorial polyhedron
        """
        CP = self.combinatorial_polyhedron()
        Vrep = [i for i, r in enumerate(self.rays()) if r[e] == 0]
        return CP.join_of_Vrep(*Vrep)

    def y_vanishing_face(self, e):
        r"""
        Return the y-vanishing face of the edge ``e``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.y_vanishing_face(0)
            A -1-dimensional face of a 3-dimensional combinatorial polyhedron
            sage: C.y_vanishing_face(1)
            A 2-dimensional face of a 3-dimensional combinatorial polyhedron
        """
        CP = self.combinatorial_polyhedron()
        ne = self._vt._ne
        Vrep = [i for i, r in enumerate(self.rays()) if r[ne + e] == 0]
        return CP.join_of_Vrep(*Vrep)

    def vanishing_face(self, e):
        r"""
        Return the vanishing face of the edge ``e``.

        The *vanishing face* of ``e`` is the face of the Delaunay polytope
        obtained by intersecting with `x_e=0` and `y_e=0`.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.vanishing_face(0)
            A -1-dimensional face of a 3-dimensional combinatorial polyhedron
            sage: C.vanishing_face(1)
            A -1-dimensional face of a 3-dimensional combinatorial polyhedron
        """
        CP = self.combinatorial_polyhedron()
        return CP.meet_of_Hrep(*self.x_vanishing_face(e).ambient_H_indices(),
                               *self.y_vanishing_face(e).ambient_H_indices())

    def forward_delaunay_face(self, e, check=True):
        r"""
        Return the forward Delaunay face of the edge ``e``.

        The edge ``e`` must be a forward flippable edge. The return face is
        a face of the corresponding combinatorial polyhedron.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.forward_delaunay_face(1)
            A 2-dimensional face of a 3-dimensional combinatorial polyhedron
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

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.backward_delaunay_face(0)
            A 2-dimensional face of a 3-dimensional combinatorial polyhedron
        """
        # y[e] = x[a] + x[d]
        if check:
            e = self._vt._check_edge(e)
            if not self._vt.is_backward_flippable(e):
                raise ValueError("non backward-flippable edge e={}".format(e))
        ne = self._vt._ne
        CP = self.combinatorial_polyhedron()
        a, b, c, d = self._vt.square_about_half_edge(2 * e)
        Vrep = [i for i, r in enumerate(self.rays()) if r[ne + e] == r[a // 2] + r[d // 2]]
        return CP.join_of_Vrep(*Vrep)

    def x_dominant_edges(self):
        r"""
        Return the subset of edges on the triangulations that are x-dominant.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,~5,7)(~0,5,~3)(1,4,8)(~1,~6,~8)(2,3,~4)(~2,~7,6)", "RBRBBBBBR")
            sage: C = vt.delaunay_cone(x_dominant_triangles=(0, 1), y_dominant_triangles=(2, 4))
            sage: C.x_dominant_edges()
            [5]
        """
        ne = self._vt.num_edges()
        return [e for e in range(self._vt.num_edges()) if all(r[e] >= r[ne + e] for r in self.rays())]

    def y_dominant_edges(self):
        r"""
        Return the subset of edges on the triangulations that are y-dominant.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,~5,7)(~0,5,~3)(1,4,8)(~1,~6,~8)(2,3,~4)(~2,~7,6)", "RBRBBBBBR")
            sage: C = vt.delaunay_cone(x_dominant_triangles=(0, 1), y_dominant_triangles=(2, 4))
            sage: C.y_dominant_edges()
            [4, 6]
        """
        ne = self._vt.num_edges()
        return [e for e in range(self._vt.num_edges()) if all(r[e] <= r[ne + e] for r in self.rays())]

    def dominated_edges(self):
        r"""
        Return the subset of edges that are either x-dominant or y-dominant.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,~5,7)(~0,5,~3)(1,4,8)(~1,~6,~8)(2,3,~4)(~2,~7,6)", "RBRBBBBBR")
            sage: C = vt.delaunay_cone(x_dominant_triangles=(0, 1), y_dominant_triangles=(2, 4))
            sage: C.dominated_edges()
            [4, 5, 6]
        """
        ne = self._vt.num_edges()
        return [e for e in range(self._vt.num_edges()) if (all(r[e] <= r[ne + e] for r in self.rays()) or
                                                           all(r[e] >= r[ne + e] for r in self.rays()))]

    def x_dominant_triangles(self):
        r"""
        Return the subset of triangles on the triangulations that are x-dominant.

        The output is a list of half-edges whose corresponding fp-orbit is a
        x-dominant triangle.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,~5,7)(~0,5,~3)(1,4,8)(~1,~6,~8)(2,3,~4)(~2,~7,6)", "RBRBBBBBR")
            sage: C = vt.delaunay_cone(x_dominant_triangles=(0, 1), y_dominant_triangles=(2, 4))
            sage: C.x_dominant_triangles()
            [0, 1]

            sage: C = vt.delaunay_cone(x_dominant_triangles=(2,), y_dominant_triangles=(0, 4))
            sage: C.x_dominant_triangles()
            [2, 3]
        """
        ne = self._vt._ne
        ans = []
        for a, b, c in self._vt.triangles():
            ex, ey = self._vt._triangle_diagonals(a)
            # r[ex] is the x-max in the triangle
            # r[ne + ey] is the y-max in the triangle
            if all(r[ex] >= r[ne + ey] for r in self.rays()):
                ans.append(a)
        return ans

    def y_dominant_triangles(self):
        r"""
        Return the subset of triangles on the triangulations that are y-dominant.

        The output is a list of half-edges whose corresponding fp-orbit is a
        y-dominant triangle.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,~5,7)(~0,5,~3)(1,4,8)(~1,~6,~8)(2,3,~4)(~2,~7,6)", "RBRBBBBBR")
            sage: C = vt.delaunay_cone(x_dominant_triangles=(0, 1), y_dominant_triangles=(2, 4))
            sage: C.y_dominant_triangles()
            [2, 3, 4, 5]

            sage: C = vt.delaunay_cone(x_dominant_triangles=(2,), y_dominant_triangles=(0, 4))
            sage: C.y_dominant_triangles()
            [0, 1, 4, 5]
        """
        ne = self._vt._ne
        ans = []
        for a, b, c in self._vt.triangles():
            ex, ey = self._vt._triangle_diagonals(a)
            # r[ex] is the x-max in the triangle
            # r[ne + ey] is the y-max in the triangle
            if all(r[ex] <= r[ne + ey] for r in self.rays()):
                ans.append(a)
        return ans

    def dominated_triangles(self):
        r"""
        Return the subset of triangles that are either x-dominant or y-dominant.

        The output is a list of half-edges whose corresponding fp-orbit is a
        y-dominant triangle.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,~5,7)(~0,5,~3)(1,4,8)(~1,~6,~8)(2,3,~4)(~2,~7,6)", "RBRBBBBBR")
            sage: C = vt.delaunay_cone(x_dominant_triangles=(0, 1), y_dominant_triangles=(2, 4))
            sage: C.dominated_triangles()
            [0, 1, 2, 3, 4, 5]

            sage: C = vt.delaunay_cone(x_dominant_triangles=(2,), y_dominant_triangles=(0, 4))
            sage: C.dominated_triangles()
            [0, 1, 2, 3, 4, 5]
        """
        ne = self._vt._ne
        ans = []
        for a, b, c in self._vt.triangles():
            ex, ey = self._vt._triangle_diagonals(a)
            # r[ex] is the x-max in the triangle
            # r[ne + ey] is the y-max in the triangle
            if all(r[ex] <= r[ne + ey] for r in self.rays()) or all(r[ex] >= r[ne + ey] for r in self.rays()):
                ans.append(a)
        return ans

    def edge_critical_face(self, e, check=True):
        r"""
        Return the edge-critical face of the edge ``e``.

        The edge-critical face associated to ``e`` is the intersection of this
        cone with the hyperplane ``x_e = y_e``. Note that it is not necessarily
        a facet.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone(x_dominant_edges=[2])
            sage: C.edge_critical_face(2)
            A 2-dimensional face of a 3-dimensional combinatorial polyhedron
            sage: C.edge_critical_face(1)
            Traceback (most recent call last):
            ...
            ValueError: the edge e=1 is neither x-dominant nor y-dominant in this cone
        """
        # x[e] = y[e]
        ne = self._vt._ne
        if check:
            e = self._vt._check_edge(e)
            if not (all(r[e] >= r[ne + e] for r in self.rays()) or
                    all(r[e] <= r[ne + e] for r in self.rays())):
                raise ValueError(f"the edge e={e} is neither x-dominant nor y-dominant in this cone")

        ne = self._vt._ne
        CP = self.combinatorial_polyhedron()
        Vrep = [i for i, r in enumerate(self.rays()) if r[e] == r[ne + e]]
        return CP.join_of_Vrep(*Vrep)

    def triangle_critical_face(self, h, check=True):
        r"""
        Return the triangle-critical face of the triangle containing ``h``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,~5,~7)(~0,5,3)(1,7,6)(~1,~3,~4)(2,~8,4)(~2,8,~6)", "RBRBRBRBB")
            sage: C = vt.delaunay_cone(x_dominant_edges=[0, 1, 2, 4, 6], y_dominant_edges=[3, 5, 7, 8], x_dominant_triangles=[2, 3, 4, 5], y_dominant_triangles=[0, 1])
            sage: C.triangle_critical_face(0)
            A 5-dimensional face of a 7-dimensional combinatorial polyhedron
            sage: C.triangle_critical_face(2)
            A 6-dimensional face of a 7-dimensional combinatorial polyhedron
        """
        ne = self._vt._ne
        if check:
            h = self._vt._check_half_edge(h)
        ex, ey = self._vt._triangle_diagonals(h)
        if check:
            if not (all(r[ex] >= r[ne + ey] for r in self.rays()) or
                    all(r[ex] <= r[ne + ey] for r in self.rays())):
                raise ValueError("the triangle of h is neither x-dominant nor y-dominant in this cone")

        CP = self.combinatorial_polyhedron()
        Vrep = []
        Vrep = [i for i, r in enumerate(self.rays()) if r[ex] == r[ne + ey]]
        return CP.join_of_Vrep(*Vrep)

    def _filter_facets(self, edges_and_faces):
        ans = collections.defaultdict(list)
        facets = {}
        for e, face in edges_and_faces:
            if face.dimension() == self.affine_dimension() - 2:
                Hrep = face.ambient_H_indices()
                ans[Hrep].append(e)
                facets[Hrep] = face
        return [(facets[Hrep], tuple(ans[Hrep])) for Hrep in facets]

    def x_vanishing_facets(self):
        r"""
        Return the list of x-vanishing facets as a list of pairs ``(face, x_vanishing_edges)``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.x_vanishing_facets()
            [(A 2-dimensional face of a 3-dimensional combinatorial polyhedron, (0,)),
             (A 2-dimensional face of a 3-dimensional combinatorial polyhedron, (2,))]
        """
        return self._filter_facets((e, self.x_vanishing_face(e)) for e in range(self._vt._ne))

    def y_vanishing_facets(self):
        r"""
        Return the list of y-vanishing facets as a list of pairs ``(face, y_vanishing_edges)``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.y_vanishing_facets()
            [(A 2-dimensional face of a 3-dimensional combinatorial polyhedron, (1,)),
             (A 2-dimensional face of a 3-dimensional combinatorial polyhedron, (2,))]
        """
        return self._filter_facets((e, self.y_vanishing_face(e)) for e in range(self._vt._ne))

    def forward_delaunay_facets(self):
        r"""
        Return the list of forward Delaunay facets as a list of pairs ``(face, flipped_edges)``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.forward_delaunay_facets()
            [(A 2-dimensional face of a 3-dimensional combinatorial polyhedron, (1,))]
        """
        return self._filter_facets((e, self.forward_delaunay_face(e)) for e in self._vt.forward_flippable_edges())

    def backward_delaunay_facets(self):
        r"""
        Return the list of backward Delaunay facets as a list of pairs ``(face, flipped_edges)``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.backward_delaunay_facets()
            [(A 2-dimensional face of a 3-dimensional combinatorial polyhedron, (0,))]
        """
        return self._filter_facets((e, self.backward_delaunay_face(e)) for e in self._vt.backward_flippable_edges())

    def edge_critical_facets(self):
        r"""
        Return the list of edge-critical facets as a list of pairs ``(face, edge)``.
        """
        return self._filter_facets((e, self.edge_critical_face(e)) for e in self.dominated_edges())

    def triangle_critical_facets(self):
        r"""
        Return the list of triangle-critical facets as a list of pairs ``(face, triangle)``.
        """
        return self._filter_facets((h, self.triangle_critical_face(h)) for h in self.dominated_triangles())

    @cached_method
    def facets_kind_and_data(self):
        r"""
        Return two list containing geometric information about the facets of this cone.

        This function mostly gathers the output of :meth:`x_vanishing_facets`,
        meth:`y_vanishing_facets`, meth:`forward_delaunay_facets` and
        :meth:`backward_delaunay_facets`.  The output is a pair of tuples
        ``(kinds, data)`` whose lengths are the number of facets of this cone.
        ``kinds[i]`` is the type of the ``i`-th facet of this cone (``'x'`` for
        x-vanishing, ``'y'`` for y-vanishing, ``'f'`` for forward Delaunay and
        ``'b'`` for backward Delaunay) and ``data[i]`` are the corresponding edges
        (either vanishing edges for x-vanishing or y-vanishing edges or flipped
        edges for forward Delaunay or backward Delaunay).

        For refined Delaunay cone, there are two additional kinds: ``'e'`` for
        edge critical and ``'t'`` for triangle critical.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.facets_kind_and_data()
            (('f', 'y', 'y', 'x', 'x', 'b'), ((1,), (2,), (1,), (2,), (0,), (0,)))

            sage: rdc = vt.refined_delaunay_cones()
            sage: for C in rdc:
            ....:     print(C.facets_kind_and_data())
            (('x', 'f', 'y', 'e'), ((2,), (1,), (1,), (0,)))
            (('e', 'f', 'y', 't', 'x'), ((2,), (1,), (1,), (0, 1), (0,)))
            (('e', 't', 'e', 'x'), ((2,), (0, 1), (1,), (0,)))
            (('e', 'y', 't', 'e'), ((0,), (1,), (0, 1), (2,)))
            (('b', 't', 'y', 'e', 'x'), ((0,), (0, 1), (1,), (2,), (0,)))
            (('b', 'e', 'y', 'x'), ((0,), (1,), (2,), (0,)))
        """
        kinds = [None] * len(self.facets())
        data = [[] for _ in range(len(self.facets()))]

        for face, edges in self.x_vanishing_facets():
            i, = face.ambient_H_indices()
            assert kinds[i] is None
            kinds[i] = 'x'
            data[i] = edges
        for face, edges in self.y_vanishing_facets():
            i, = face.ambient_H_indices()
            assert kinds[i] is None
            kinds[i] = 'y'
            data[i] = edges
        for face, edges in self.forward_delaunay_facets():
            i, = face.ambient_H_indices()
            assert kinds[i] is None
            kinds[i] = 'f'
            data[i] = edges
        for face, edges in self.backward_delaunay_facets():
            i, = face.ambient_H_indices()
            assert kinds[i] is None
            kinds[i] = 'b'
            data[i] = edges
        for face, edges in self.edge_critical_facets():
            i, = face.ambient_H_indices()
            assert kinds[i] is None
            kinds[i] = 'e'
            data[i] = edges
        for face, half_edges in self.triangle_critical_facets():
            i, = face.ambient_H_indices()
            assert kinds[i] is None
            kinds[i] = 't'
            data[i] = half_edges

        assert not any(v is None for v in kinds)
        return tuple(kinds), tuple(data)


def incidence_matrix(facets, rays, mutable=False):
    r"""
    Return the incidence matrix of the given ``facets`` and ``rays`` given
    as list of vectors.

    EXAMPLES::

        sage: from veerer.delaunay_cone import incidence_matrix
        sage: V = FreeModule(ZZ, 3)
        sage: facets = [V((2, -1, 1)), V((1, 0, 1)), V((1, -2, 1)), V((4, -5, 2))]
        sage: rays = [V((-1, -1, 1)), V((-1, 0, 2)), V((1, 0, -1)), V((1, 2, 3))]
        sage: incidence_matrix(facets, rays)
        [1 1 0 0]
        [1 0 0 1]
        [0 1 1 0]
        [0 0 1 1]
    """
    ans = matrix(ZZ, len(rays), len(facets))
    for i, r in enumerate(rays):
        for j, f in enumerate(facets):
            ans[i, j] = r.dot_product(f).is_zero()
    if not mutable:
        ans.set_immutable()
    return ans
