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
    The Delaunay cone associated to a veering triangulation of holomorphic or meromorphic differentials.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily
        sage: from veerer.delaunay_cone import DelaunayCone

        sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~7,~5)(~3,~4,~2)(~6,~1,~8)", "RRBRRBRRB")
        sage: gp = DelaunayCone(vt)
        sage: gp
        DelaunayCone of VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~8,~6,~1)(~7,~5,~0)(~4,~2,~3)", "RRBRRBRRB") of dimension 8 made of 2 forward-flip facets 3 backward-flip facets 5 x-degeneration facets and 4 y-degeneration facets
        sage: gp.num_facets()
        (2, 3, 5, 4)

        sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~1,~5)(~3,~7,~8)(~6,~4,~2)", "RRBRRBRBB")
        sage: gp = DelaunayCone(vt)
        sage: gp.num_facets()
        (3, 2, 4, 4)
    """
    def __init__(self, vt):
        self._vt = vt
        self._cone = vt.delaunay_cone()
        if self._cone.affine_dimension() != 2 * self._vt.dimension():
            raise ValueError('not Delaunay')
        self._subspace = Subspace(matrix(self._cone.eqns()))
        self._L = LinearExpressions(vt.base_ring())
        ne = self._vt.num_edges()
        x = self._x = [self._L.variable(e) for e in range(ne)]
        y = self._y = [self._L.variable(ne + e) for e in range(ne)]

        # facets initialization
        V = self._subspace
        pfacets = []
        for ieq in self._cone.ieqs():
            pieq = V.lin_project(V.ambient_module(ieq))
            pieq = vector_normalize(vt.base_ring(), pieq)
            pieq.set_immutable()
            pfacets.append(pieq)

        ep = vt._ep
        hyperplanes = []
        for e in range(vt._n):
            if ep[e] < e:
                break
            hyperplanes.append((e, x[vt._norm(e)] == 0))
        x_degeneration_facets = filter_facets(self._subspace, pfacets, hyperplanes)
        self._xfacets = x_degeneration_facets

        hyperplanes = []
        for e in range(vt._n):
            if ep[e] < e:
                break
            hyperplanes.append((e, y[vt._norm(e)] == 0))
        y_degeneration_facets = filter_facets(self._subspace, pfacets, hyperplanes)
        self._yfacets = y_degeneration_facets

        hyperplanes = []
        for e in vt.forward_flippable_edges():
            a, b, c, d = vt.square_about_edge(e)
            hyperplanes.append((e, x[vt._norm(e)] == y[vt._norm(a)] + y[vt._norm(d)]))
        forward_flip_facets = filter_facets(self._subspace, pfacets, hyperplanes)
        self._ffacets = forward_flip_facets

        hyperplanes = []
        for e in vt.backward_flippable_edges():
            a, b, c, d = vt.square_about_edge(e)
            hyperplanes.append((e, y[vt._norm(e)] == x[vt._norm(a)] + x[vt._norm(d)]))
        backward_flip_facets = filter_facets(self._subspace, pfacets, hyperplanes)
        self._bfacets = backward_flip_facets

        self._limits = [len(x_degeneration_facets)]
        self._limits.append(self._limits[0] + len(y_degeneration_facets))
        self._limits.append(self._limits[1] + len(forward_flip_facets))
        self._limits.append(self._limits[2] + len(backward_flip_facets))

        self._facets = tuple(h for h, data in x_degeneration_facets) +\
                       tuple(h for h, data in y_degeneration_facets) +\
                       tuple(h for h, data in forward_flip_facets) +\
                       tuple(h for h, data in backward_flip_facets)

    def __repr__(self):
        s = "DelaunayCone of {} of dimension {} made of"
        s += " {} forward-flip facets"
        s += " {} backward-flip facets"
        s += " {} x-degeneration facets"
        s += " and {} y-degeneration facets"
        return s.format(self._vt, self._cone.affine_dimension(), len(self._ffacets), len(self._bfacets), len(self._xfacets), len(self._yfacets))

    @cached_method
    def pfacets(self):
        r"""
        Return the projections (relative to the equations) of the inequalities
        that matter in this polytope.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: G = DelaunayCone(T)
            sage: sorted(G.pfacets())
            [(0, 0, 0, 1), (0, 0, 1, 0), (0, 1, 0, 0), (1, -1, 0, 0), (1, 0, -1, -2), (1, 1, -1, -1)]
        """
        return self._facets

    @cached_method
    def prays(self):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~7,~5)(~3,~4,~2)(~6,~1,~8)", "RRBRRBRRB")
            sage: gp = DelaunayCone(vt)
            sage: sorted(gp.prays())
            [(0, 0, 0, 0, 0, 1, 0, 1),
             (0, 0, 0, 1, 0, -1, 0, 0),
             (0, 1, 0, -2, 0, 1, 0, 0),
            ...
             (4, -1, 0, 2, -1, -1, 2, 0),
             (4, 0, 0, 0, -1, -1, 2, 0),
             (4, 0, 0, 1, -1, -1, 2, 0)]

            sage: from veerer.linear_family import VeeringTriangulationLinearFamilies
            sage: X = VeeringTriangulationLinearFamilies.prototype_H1_1(0, 2, 1, -1)
            sage: gp = DelaunayCone(X)
            sage: sorted(gp.prays())
            [(0, 0, 1, -1, 0, 0),
             (0, 1, 1, 0, 0, 0),
             (1, 0, 1, -1, 0, 0),
            ...
             (2, 2, 2, -1, 0, -1),
             (2, 2, 3, -1, -1, -1),
             (6, 4, 7, -4, -1, -4)]
        """
        V = self._subspace
        res = []
        for ray in self._cone.rays():
            pray = V.vec_project(V.ambient_module(ray))
            pray = vector_normalize(V.base_ring(), pray)
            pray.set_immutable()
            res.append(pray)
        res.sort()
        return tuple(res)

    def facet_index_kind(self, h):
        if h < self._limits[0]:
            return ('x', self._xfacets[h][1])
        elif h < self._limits[1]:
            return ('y', self._yfacets[h - self._limits[0]][1])
        elif h < self._limits[2]:
            return ('f', self._ffacets[h - self._limits[1]][1])
        else:
            return ('b', self._bfacets[h - self._limits[2]][1])

    def edge_degenerations(self):
        r"""
        Iterate through subsets of admissible edge degenerations of given complex codimension ``codim``.

        Warning: we do not check for the "boundary of cylinder" condition.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: vt = VeeringTriangulation("(0,8,~7)(1,3,~2)(2,10,~3)(4,6,~5)(5,11,~6)(7,~9,~8)(9,~11,~10)(~4,~1,~0)", "RRBRBBRRBRRB")
            sage: C = DelaunayCone(vt)
            sage: list(C.edge_degenerations())
            [(2,),
             (6,),
             (8,),
             (2, 6),
             (2, 8),
             (6, 8),
             (2, 6, 8),
             (4, 5, 6, 11),
             (2, 4, 5, 6, 11),
             (4, 5, 6, 8, 11),
             (2, 4, 5, 6, 8, 11)]

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~7,~5)(~3,~4,~2)(~6,~1,~8)", "RRBRRBRRB")
            sage: C = DelaunayCone(vt)
            sage: list(C.edge_degenerations())
            [(8,), (2, 5), (2, 5, 8), (2, 3, 4, 5), (2, 3, 4, 5, 8), (0, 1, 2, 5, 6, 7, 8)]

            sage: vt = VeeringTriangulation("(0,~7,6)(1,~5,~2)(2,4,~3)(3,11,~4)(5,10,~6)(7,9,~8)(8,~10,~9)(~11,~1,~0)", "RBRBRRBRBRRR")
            sage: C = DelaunayCone(vt)
            sage: list(C.edge_degenerations())
            [(1,),
             (3,),
             (6,),
             (8,),
             (1, 3),
             (1, 6),
             (3, 8),
             (6, 8),
             (1, 3, 6),
             (1, 6, 8),
             (1, 3, 6, 8)]
        """
        dim = self._cone.space_dimension()
        ne = self._vt.num_edges()

        def completion(vanishing_edges, vanishing_cone):
            cs = ConstraintSystem(dim)
            for e in vanishing_edges:
                cs.insert(self._x[e] == 0)
                cs.insert(self._y[e] == 0)

            done = False
            while not done:
                # print('new loop')
                vanishing_cone = vanishing_cone.add_constraints(cs)

                # print('current cone dimension={}'.format(vanishing_cone.affine_dimension()))
                vanishing_indices = [True] * (2 * ne)
                for r in vanishing_cone.rays():
                    for i in range(2 * ne):
                        if r[i]:
                            vanishing_indices[i] = False
                done = True
                for i in range(ne):
                    num = vanishing_indices[i] + vanishing_indices[ne + i]
                    if num == 0:
                        # print('i={} in Eup'.format(i))
                        pass
                    elif num == 1:
                        # print('i={} partial vanishing'.format(i))
                        cs.insert(self._x[i] == 0)
                        cs.insert(self._y[i] == 0)
                        done = False
                        vanishing_edges.add(i)
                    elif num == 2:
                        # print('i={} in Elow'.format(i))
                        vanishing_edges.add(i)

        # 1. for each edge, we compute inductively what needs to degenerate
        # on the V-representation we can get the list of vanishing edges
        ne = self._vt.num_edges()
        ans = [set() for _ in range(ne + 1)]
        for e in range(ne):
            vanishing_edges = set([e])
            completion(vanishing_edges, self._cone)
            ans[len(vanishing_edges)].add(frozenset(vanishing_edges))
        for i in range(1, ne):
            for edges1 in ans[i]:
                for j in range(1, i + 1):
                    for edges2 in ans[j]:
                        if edges1 != edges2:
                            vanishing_edges = set().union(edges1, edges2)
                            completion(vanishing_edges, self._cone)
                            ans[len(vanishing_edges)].add(frozenset(vanishing_edges))

        # TODO: maybe we could remove the tuple(sorted(...)) and the sorted(...)
        # but it is probably not the bottleneck of the computation
        output = []
        for i in range(1, ne):
            output.extend(sorted(tuple(sorted(t)) for t in ans[i]))
        return output

    def num_facets(self):
        r"""
        Return the number of facets of each kind (forward flip, backward flip, x degeneration, y degeneration)
        """
        return (len(self.forward_flip_facets()),
                len(self.backward_flip_facets()), 
                len(self.x_degeneration_facets()),
                len(self.y_degeneration_facets()))

    def forward_flip_facets(self):
        r"""
        Return the list of forward-flip facets.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: G = DelaunayCone(T)
            sage: G.forward_flip_facets()
            (((1, 0, -1, -2), [1]),)
        """
        return self._ffacets

    def backward_flip_facets(self):
        r"""
        Return the list of backward-flip facets.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: G = DelaunayCone(T)
            sage: G.backward_flip_facets()
            (((1, 1, -1, -1), [0]),)
        """
        return self._bfacets

    def x_degeneration_facets(self):
        r"""
        Return the list of x-degeneration facets.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: G = DelaunayCone(T)
            sage: G.x_degeneration_facets()
            (((0, 1, 0, 0), [2]), ((1, -1, 0, 0), [0]))
        """
        return self._xfacets

    def y_degeneration_facets(self):
        r"""
        Return the list of y-degeneration facets.

        EXAMPLES:

            sage: from veerer import VeeringTriangulation
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: G = DelaunayCone(T)
            sage: G.y_degeneration_facets()
            (((0, 0, 0, 1), [2]), ((0, 0, 1, 0), [1]))
        """
        return self._yfacets

    @cached_method
    def incidence_matrix(self):
        r"""
        Columns correspond to inequalities the rows correspond to rays.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: from veerer.delaunay_cone import DelaunayCone

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: G = DelaunayCone(T)
            sage: G.incidence_matrix()
            [1 0 0 1 0 1]
            [1 0 1 0 1 1]
            [0 1 0 1 0 1]
            [0 1 1 0 1 0]
            [0 1 1 0 0 1]
            [1 0 0 1 1 0]
            [0 1 0 1 1 0]
        """
        rays = self.prays()
        facets = self.pfacets()
        ans = matrix(ZZ, len(rays), len(facets))
        for i, r in enumerate(rays):
            for j, f in enumerate(facets):
                ans[i, j] = r.dot_product(f).is_zero()
        ans.set_immutable()
        return ans


class Subspace:
    r"""
    EXAMPLES::

        sage: from veerer.delaunay_cone import Subspace

        sage: m = matrix([[1, 1, 1, 1, 1], [5, 1, 13, 2, 7]])
        sage: S = Subspace(m)
        sage: S
        Subspace defined by
        equations: [(1, 1, 1, 1, 1), (5, 1, 13, 2, 7)]
        generators: [(0, -1, -1, 0, 2), (-2, 0, 1, 2, -1), (-1, 2, 0, -2, 1)]
        sage: S.lin_project(vector([1, 1, 1, 1, 1]))
        (0, 0, 0)
        sage: S.lin_project(vector([1, 2, 3, 4, 5]))
        (5, 4, 0)
        sage: a, b, c = S.basis()
        sage: S.vec_project(3 * a - 2 * b + c)
        (3, -2, 1)

    Of course, the projection preserves the evaluation of linear forms on vectors::

        sage: l = vector([1, 2, 3, 4, 5])
        sage: v = 3 * a - 2 * b + c
        sage: l.dot_product(v)
        7
        sage: S.lin_project(l).dot_product(S.vec_project(v))
        7
    """
    def __init__(self, eqns, base_ring=None):
        if base_ring is None:
            base_ring = eqns.base_ring()

        self.ambient_module = eqns.row_ambient_module()

        # TODO: the generator basis of the subspace we pick should
        # probably be LLL-ized rather than echelonized
        self._eqns = eqns
        self._eqns_lll, self._eqns_good_basis = eqns.LLL(transformation=True)
        assert self._eqns_lll.rank() == self._eqns_lll.nrows()

        assert self._eqns_good_basis * self._eqns == self._eqns_lll

        self._gens = (self._eqns_lll.right_kernel_matrix()).LLL()
        assert all((self._eqns * v).is_zero() for v in self._gens.rows())

        self._base_ring = base_ring

        self._ambient_dim = eqns.ncols()
        self._codim = eqns.nrows()
        self._dim = self._ambient_dim - self._codim

        self.free_module = FreeModule(base_ring, self._dim)

    def __repr__(self):
        return 'Subspace defined by\nequations: {}\ngenerators: {}'.format(self._eqns.rows(), self._gens.rows())

    def base_ring(self):
        return self._base_ring

    def ambient_dimension(self):
        return self._ambient_dim

    def dimension(self):
        return self._dim

    def basis(self):
        return self._gens.rows()

    def lin_project(self, l):
        r"""
        Return a canonical form for ``l`` restricted to self.

        This is done by evaluating ``l`` on a fixed (rather nice) basis.
        """
        return self.free_module([l.dot_product(v) for v in self._gens.rows()])

    def vec_project(self, v):
        return self._gens.solve_left(v)


def filter_facets(V, facets, hyperplanes):
    r"""
    - ``V`` - the linear subspace associated to P to do projections

    - ``facets`` - facets of P reduced in the basis of V

    - ``hyperplanes`` - a bunch of labels and hyperplanes
    """
    base_ring = V.base_ring()
    dim = V.ambient_dimension()
    facets = {f: [] for f in facets}
    for e, constraint in hyperplanes:
        constraint = constraint.coefficients(dim=dim, homogeneous=True)
        constraint = V.ambient_module(constraint)
        pconstraint = V.lin_project(constraint)
        pconstraint = vector_normalize(base_ring, pconstraint)
        pconstraint.set_immutable()
        if pconstraint in facets:
            # the constraint is an actual facet
            facets[pconstraint].append(e)

    return tuple((pieq, edges) for pieq, edges in facets.items() if edges)
