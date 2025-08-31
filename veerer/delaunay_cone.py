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

    The cone is embedded in `R^{2 ne}` where `ne` is the number of edges of the
    underlying veering triangulation. The first ``ne`` coordinates indexed by
    ``0, 1, ..., ne-1`` are the horizontal or `x`-coordinates while the last
    ``ne`` coordinates index by ``ne, ne+1, ..., 2ne-1``.

    This class is usally not constructed via its constructor but via the function
    :meth:`~veerer.veering_triangulation.delaunay_cone`.

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
        nx = len(self.x_vanishing_facets())
        ny = len(self.y_vanishing_facets())
        s = "{}-dimensional Delaunay cone made of\n".format(self.affine_dimension())
        s += " {} forward-flip facet{}\n".format(nf, "s" if nf >= 2 else "")
        s += " {} backward-flip facet{}\n".format(nb, "s" if nb >= 2 else "")
        s += " {} x-degeneration facet{}\n".format(nx, "s" if nx >= 2 else "")
        s += " {} y-degeneration facet{}".format(ny, "s" if ny >= 2 else "")
        print(s)

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

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: C = vt.delaunay_cone()
            sage: C.facets_kind_and_data()
            (('f', 'y', 'y', 'x', 'x', 'b'), ((1,), (2,), (1,), (2,), (0,), (0,)))
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

        assert not any(v is None for v in kinds)
        return tuple(kinds), tuple(data)


def incidence_matrix(facets, rays, mutable=False):
        ans = matrix(ZZ, len(rays), len(facets))
        for i, r in enumerate(rays):
            for j, f in enumerate(facets):
                ans[i, j] = r.dot_product(f).is_zero()
        if not mutable:
            ans.set_immutable()
        return ans
