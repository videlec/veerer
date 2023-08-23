r"""
Linear family of coordinates on a veering triangulation
"""

######################################################################
# This file is part of veering.
#
#       Copyright (C) 2023 Vincent Delecroix
#
# veerer is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# veerer is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with veerer. If not, see <https://www.gnu.org/licenses/>.
######################################################################

from array import array
from copy import copy
import collections
import itertools

from .env import sage, ppl
from .constants import VERTICAL, HORIZONTAL, BLUE, RED
from .permutation import perm_cycle_string, perm_cycles, perm_check, perm_conjugate, perm_on_list
from .linear_expression import LinearExpressions, ConstraintSystem, polyhedron, polyhedron_add_constraints, polyhedron_dimension, polyhedron_to_hashable


from .veering_triangulation import VeeringTriangulation

if sage is not None:
    from sage.structure.element import get_coercion_model
    from sage.matrix.constructor import matrix
    from sage.geometry.polyhedron.constructor import Polyhedron

    cm = get_coercion_model()
else:
    matrix = None
    Polyhedron = None

    cm = None


def subspace_are_equal(subspace1, subspace2, check=True):
    r"""
    Test whether the subspaces generated by the rows of ``subspace1`` and
    ``subspace2`` are equal.

    INPUT:

    - ``subspace1``, ``subspace2`` -- full rank matrices with the same number
      of columns

    - ``check`` -- boolean (default ``True``)

    EXAMPLES::

        sage: from veerer.linear_family import subspace_are_equal

        sage: m1 = random_matrix(ZZ, 3, 5)
        sage: m2 = copy(m1)
        sage: m2.add_multiple_of_row(0, 1, -2)
        sage: m2.add_multiple_of_row(0, 2, 1)
        sage: m2.add_multiple_of_row(1, 2, 1)
        sage: subspace_are_equal(m1, m2)
        True

        sage: m1 = matrix(ZZ, [[1, 1, 0]])
        sage: m2 = matrix(ZZ, [[1, 1, -1]])
        sage: subspace_are_equal(m1, m2)
        False
    """
    if check:
        if subspace1.ncols() != subspace2.ncols():
            raise ValueError('subspace1 and subspace2 of different ambient dimensions')
        if subspace1.rank() != subspace1.nrows():
            raise ValueError('subspace1 not full rank')
        if subspace2.rank() != subspace2.nrows():
            raise ValueErrror('subspace2 not full rank')

    n = subspace1.nrows()
    if n != subspace2.nrows():
        return False

    base_ring = cm.common_parent(subspace1.base_ring(), subspace2.base_ring())
    mat = matrix(base_ring, n + 1, subspace1.ncols())
    mat[:n] = subspace1
    for v in subspace2.rows():
        mat[n] = v
        r = mat.rank()
        if r < n:
            raise RuntimeError('matrices where expected to be full rank')
        if r > n:
            return False
    return True


def subspace_cmp(subspace1, subspace2, check=True):
    if check:
        if subspace1.ncols() != subspace2.ncols():
            raise ValueError('subspace1 and subspace2 of different ambient dimensions')
        if subspace1.rank() != subspace1.nrows():
            raise ValueError('subspace1 not full rank')
        if subspace2.rank() != subspace2.nrows():
            raise ValueErrror('subspace2 not full rank')

    n = subspace1.nrows()
    if n != subspace2.nrows():
        return False

    base_ring = cm.common_parent(subspace1.base_ring(), subspace2.base_ring())
    subspace1 = subspace1.echelon_form()
    subspace2 = subspace2.echelon_form()
    for r1, r2 in zip(subspace1, subspace2):
        c = (r1 > r2) - (r1 < r2)
        if c:
            return c
    return 0

def relabel_on_edges(ep, r, n, m):
    r"""
    INPUT:

    - ep - edge permutation

    - r - relabelling permutation on half edges (list of length n)

    - n - num half edges

    - m - num edges

    OUTPUT: list of length m

    EXAMPLES::

        sage: from array import array
        sage: from veerer.linear_family import relabel_on_edges

        sage: ep = array('l', [8, 1, 2, 7, 4, 5, 6, 3, 0])
        sage: r = array('l', [3, 0, 5, 4, 6, 2, 1, 8, 7])
        sage: relabel_on_edges(ep, r, 9, 7)
        array('l', [3, 0, 5, 4, 6, 2, 1])
    """
    rr = array('l', [-1] * m)
    for i in range(m):
        if ep[i] < i:
            raise ValueError("not in canonical form")
        j = r[i]
        k = r[ep[i]]
        if (j >= m and k >= m):
            raise ValueError("relabelling not preserving canonical form")
        if j < k:
            rr[i] = j
        else:
            rr[i] = k
    return rr


def matrix_permutation(mat, perm):
    m = mat.ncols()
    for c in perm_cycles(perm, False, m):
        for i in range(1, len(c)):
            mat.swap_columns(c[0], c[i])


class VeeringTriangulationLinearFamily(VeeringTriangulation):
    r"""
    Veering triangulation together with a subspace of H^1(S, Sigma; \bR) that
    describes a (piece of a) linear GL(2,R)-invariant immersed sub-orbifold.
    """
    __slots__ = ['_subspace']

    def __init__(self, *args, mutable=False, check=True):
        if len(args) == 2:
            vt, subspace = args
            t = vt
            colouring = vt._colouring
        elif len(args) == 3:
            t, colouring, subspace = args
        VeeringTriangulation.__init__(self, t, colouring, mutable=mutable, check=False)

        if not isinstance(subspace, sage.structure.element.Matrix):
            subspace = matrix(subspace)

        self._subspace = subspace
        self._subspace.echelonize()
        if not mutable:
            self._subspace.set_immutable()

        if check:
            self._check(ValueError)

    def _horizontal_subspace(self):
        mat = copy(self._subspace)
        ne = self.num_edges()
        ep = self._ep
        for j in range(ne):
            if ep[j] < j:
                raise ValueError('not in standard form')
            if self._colouring[j] == BLUE:
                for i in range(mat.nrows()):
                    mat[i, j] *= -1
        return mat

    def ambient_dimension(self):
        return self._subspace.nrows()

    def conjugate(self):
        raise NotImplementedError

    def rotate(self):
        r"""
        Conjugate this family.

        EXAMPLES::

            sage: from veerer import *

            sage: fp = "(0,1,2)(~0,~4,~2)(3,4,5)(~3,~1,~5)"
            sage: cols = "BRRBRR"
            sage: f = VeeringTriangulation(fp, cols).as_linear_family(mutable=True)
            sage: f.rotate()
            sage: f
            VeeringTriangulationLinearFamily("(0,1,2)(3,4,5)(~5,~3,~1)(~4,~2,~0)", "RBBRBB", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 1, 1), (0, 0, 0, 1, 0, -1)])

 
            sage: fp = "(0,12,~11)(1,13,~12)(2,14,~13)(3,15,~14)(4,17,~16)(5,~10,11)(6,~3,~17)(7,~2,~6)(8,~5,~7)(9,~0,~8)(10,~4,~9)(16,~15,~1)"
            sage: cols = "RRRRRRBBBBBBBBBBBB"
            sage: f = VeeringTriangulation(fp, cols).as_linear_family(mutable=True)
            sage: f.rotate()
            sage: f
            VeeringTriangulationLinearFamily("(0,12,~11)(1,13,~12)(2,14,~13)(3,15,~14)(4,17,~16)(5,~10,11)(6,~3,~17)(7,~2,~6)(8,~5,~7)(9,~0,~8)(10,~4,~9)(16,~15,~1)", "BBBBBBRRRRRRRRRRRR", [(1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0), (0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 2, 1, 1, 1, 0, 0), (0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1), (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0), (0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)])
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation family; use a mutable copy instead')

        subspace = self._horizontal_subspace()
        subspace.echelonize()
        VeeringTriangulation.rotate(self)
        self._subspace = subspace

        # TODO: remove check
        self._check()

    def _set_subspace_constraints(self, insert, x, slope):
        ambient_dim = self._subspace.ncols()
        if slope == VERTICAL:
            subspace = self._subspace
        elif slope == HORIZONTAL:
            subspace = self._horizontal_subspace()
        for row in subspace.right_kernel_matrix():
            insert(sum(row[i] * x[i] for i in range(ambient_dim)) == 0)

    def copy(self, mutable=None):
        r"""
        Return a copy of this linear family.
        """
        if mutable is None:
            mutable = self._mutable

        if not self._mutable and not mutable:
            # avoid copies of immutable objects
            return self

        L = VeeringTriangulationLinearFamily.__new__(VeeringTriangulationLinearFamily)
        L._n = self._n
        L._vp = self._vp[:]
        L._ep = self._ep[:]
        L._fp = self._fp[:]
        L._colouring = self._colouring[:]
        L._subspace = copy(self._subspace)
        L._mutable = mutable
        if not mutable:
            L._subspace.set_immutable()
        return L

    def base_ring(self):
        return self._subspace.base_ring()

    def set_immutable(self):
        VeeringTriangulation.set_immutable(self)
        self._subspace.set_immutable()

    def __hash__(self):
        r"""
        TESTS::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: h = hash(vt.as_linear_family())
        """
        if self._mutable:
            raise ValueError('mutable veering triangulation linear family not hashable')

        x = 140737488617563
        x = ((x ^ hash(self._vp.tobytes())) * 2147483693) + 82520 + self._n + self._n
        x = ((x ^ hash(self._ep.tobytes())) * 2147483693) + 82520 + self._n + self._n
        x = ((x ^ hash(self._fp.tobytes())) * 2147483693) + 82520 + self._n + self._n
        x = ((x ^ hash(self._colouring.tobytes())) * 2147483693) + 82520 + self._n + self._n
        x = ((x ^ hash(self._subspace) * 2147483693)) + 82520 + self._n + self._n

        return x

    def __str__(self):
        r"""
        Return a string representation.

        TESTS::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", [RED, RED, BLUE])
            sage: str(vt.as_linear_family())
            'VeeringTriangulationLinearFamily("(0,1,2)(~2,~0,~1)", "RRB", [(1, 0, -1), (0, 1, 1)])'
        """
        return "VeeringTriangulationLinearFamily(\"{}\", \"{}\", {})".format(
               perm_cycle_string(self._fp, False, self._n, self._ep),
               self._colouring_string(short=True),
               self._subspace.rows())

    def __repr__(self):
        return str(self)

    def _check(self, error=ValueError):
        subspace = self._subspace
        VeeringTriangulation._check(self, error)
        if subspace.ncols() != self.num_edges():
            raise error('subspace matrix has wrong dimension')
        if subspace.rank() != subspace.nrows():
            raise error('subspace matrix is not of full rank')
        # test that elements satisfy the switch condition
        for v in subspace.rows():
            self._set_switch_conditions(self._tt_check, v, VERTICAL)
        if subspace != subspace.echelon_form():
            raise error('subspace not in echelon form')
        if self._mutable != self._subspace.is_mutable():
            raise error('incoherent mutability states')

    def __eq__(self, other):
        r"""
        TESTS::

            sage: from veerer import *
            sage: vt, s, t = VeeringTriangulations.L_shaped_surface(1,1,1,1)
            sage: s = vector(QQ, s)
            sage: t = vector(QQ, t)
            sage: f1 = VeeringTriangulationLinearFamily(vt, [s, t])
            sage: f2 = VeeringTriangulationLinearFamily(vt, [s + 2*t, -s - t])
            sage: f1 == f2
            True
            sage: from veerer import *
            sage: vt2, s2, t2 = VeeringTriangulations.L_shaped_surface(1,2,1,3)
            sage: f3 = VeeringTriangulationLinearFamily(vt2, [s2, t2])
            sage: f1 == f3
            False
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", [RED, RED, BLUE])
            sage: vt.as_linear_family() == f1
            False
        """
        if type(self) is not type(other):
            raise TypeError
        return VeeringTriangulation.__eq__(self, other) and self._subspace == other._subspace

    def __ne__(self, other):
        r"""
        TESTS::

            sage: from veerer import *
            sage: vt, s, t = VeeringTriangulations.L_shaped_surface(1,1,1,1)
            sage: s = vector(QQ, s)
            sage: t = vector(QQ, t)
            sage: f1 = VeeringTriangulationLinearFamily(vt, [s, t])
            sage: f2 = VeeringTriangulationLinearFamily(vt, [s + 2*t, -s - t])
            sage: f1 != f2
            False
            sage: from veerer import *
            sage: vt2, s2, t2 = VeeringTriangulations.L_shaped_surface(1,2,1,3)
            sage: f3 = VeeringTriangulationLinearFamily(vt2, [s2, t2])
            sage: f1 != f3
            True
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", [RED, RED, BLUE])
            sage: vt.as_linear_family() != f1
            True
        """
        if type(self) is not type(other):
            raise TypeError
        return VeeringTriangulation.__ne__(self, other) or self._subspace != other._subspace

    def _richcmp_(self, other, op):
        c = (self._n > other._n) - (self._n < other._n)
        if c:
            return rich_to_bool(op, c)

        c = (self._colouring > other._colouring) - (self._colouring < other._colouring)
        if c:
            return rich_to_bool(op, c)

        c = (self._fp > other._fp) - (self._fp < other._fp)
        if c:
            return rich_to_bool(op, c)

        c = (self._ep > other._ep) - (self._ep < other._ep)
        if c:
            return rich_to_bool(op, c)

        c = subspace_cmp(self._subspace, other._subspace)
        return rich_to_bool(op, c)

    def train_track_polytope(self, slope=VERTICAL, low_bound=0, backend='ppl'):
        r"""
        Return the polytope of non-negative elements in the subspace.

        EXAMPLES::

            sage: from veerer import *
            sage: vt, s, t = VeeringTriangulations.L_shaped_surface(1, 3, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(vt, [s, t])
            sage: f.train_track_polytope(VERTICAL)
            A 2-dimensional polyhedron in QQ^7 defined as the convex hull of 1 point, 2 rays
            sage: f.train_track_polytope(HORIZONTAL)
            A 2-dimensional polyhedron in QQ^7 defined as the convex hull of 1 point, 2 rays

            sage: f.train_track_polytope(VERTICAL, backend='ppl').generators()
            Generator_System {point(0/1, 0/1, 0/1, 0/1, 0/1, 0/1, 0/1), ray(0, 1, 3, 3, 1, 1, 0), ray(1, 0, 0, 1, 1, 1, 1)}
            sage: f.train_track_polytope(HORIZONTAL, backend='ppl').generators()
            Generator_System {point(0/1, 0/1, 0/1, 0/1, 0/1, 0/1, 0/1), ray(1, 0, 0, 1, 1, 1, 1), ray(3, 1, 3, 0, 2, 2, 3)}
        """
        ne = self.num_edges()
        L = LinearExpressions(self.base_ring())
        cs = ConstraintSystem()
        for i in range(ne):
            cs.insert(L.variable(i) >= low_bound)
        self._set_subspace_constraints(cs.insert, [L.variable(i) for i in range(ne)], slope)
        return polyhedron(cs, backend)

    def dimension(self):
        r"""
        Return the dimension of the linear family.
        """
        return self._subspace.nrows()

    def is_core(self, method='polytope'):
        r"""
        Test whether this linear family is core.

        It is core, if the dimension of the polytope given by the train-track
        and non-negativity conditions is full dimensional in the subspace.

        EXAMPLES::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", [RED, RED, BLUE])
            sage: vt.as_linear_family().is_core()
            True
            sage: VeeringTriangulationLinearFamily(vt, [1, 0, -1]).is_core()
            False
        """
        if method == 'polytope':
            return self.train_track_polytope().dimension() == self._subspace.nrows()
        else:
            raise NotImplementedError

    def relabel(self, p, check=True):
        r"""
        Relabel inplace the veering triangulation linear family according to the permutation ``p``.

        Relabelling the subspace as well::

            sage: from veerer import VeeringTriangulations, VeeringTriangulationLinearFamily
            sage: from veerer.permutation import perm_random_centralizer

            sage: vt, s, t = VeeringTriangulations.L_shaped_surface(2, 3, 4, 5, 1, 2)
            sage: f = VeeringTriangulationLinearFamily(vt, [s, t], mutable=True)
            sage: for _ in range(10):
            ....:     p = f._relabelling_from(choice(range(9)))
            ....:     f.relabel(p)
            ....:     f._check()

            sage: for _ in range(10):
            ....:     p = perm_random_centralizer(f.edge_permutation(copy=False))
            ....:     f.relabel(p)
            ....:     f._check()
        """
        n = self.num_half_edges()
        m = self.num_edges()
        ep = self._ep
        if check and not perm_check(p, n):
            p = perm_init(p, n, ep)
            if not perm_check(p, n):
                raise ValueError('invalid relabelling permutation')

        rr = relabel_on_edges(self._ep, p, n, m)
        matrix_permutation(self._subspace, rr)
        self._subspace.echelonize()
        VeeringTriangulation.relabel(self, p, False)

        # TODO: remove check
        self._check()

    def best_relabelling(self, all=False):
        n = self.num_half_edges()
        m = self.num_edges()

        best = None
        if all:
            relabellings = []

        for start_edge in self._automorphism_good_starts():
            relabelling = self._relabelling_from(start_edge)
            rr = relabel_on_edges(self._ep, relabelling, n, m)

            fp = perm_conjugate(self._fp, relabelling)
            ep = perm_conjugate(self._ep, relabelling)
            cols = self._colouring[:]
            perm_on_list(relabelling, cols)
            subspace = copy(self._subspace)
            matrix_permutation(subspace, rr)
            subspace.echelonize()
            subspace.set_immutable()

            T = (cols, fp, ep, subspace)
            if best is None or T < best:
                best = T
                best_relabelling = relabelling
                if all:
                    del relabellings[:]
                    relabellings.append(relabelling)
            elif all and T == best:
                relabellings.append(relabelling)

        return (relabellings, best) if all else (best_relabelling, best)

    # TODO: change to canonicalize ? Since we also need to canonicalize the subspace
    # it is not only about labels
    def _non_isom_easy(self, other):
        return (VeeringTriangulation._non_isom_easy(self, other) or
                self._subspace.nrows() != other._subspace.nrows())

    def flip(self, e, col, check=True):
        r"""
        EXAMPLES::

            sage: from veerer import *

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)

            sage: L = VeeringTriangulationLinearFamily(T, [s, t], mutable=True)
            sage: T = T.copy(mutable=True)

            sage: T.flip(3, 2)
            sage: L.flip(3, 2)
            sage: T
            VeeringTriangulation("(0,3,2)(1,4,~0)(5,6,~1)", "BRRBBBB")
            sage: L
            VeeringTriangulationLinearFamily("(0,3,2)(1,4,~0)(5,6,~1)", "BRRBBBB", [(1, 0, 0, 1, 1, 1, 1), (0, 1, 1, -1, 1, 1, 0)])

            sage: L.flip(4, 2)
            sage: T.flip(4, 2)
            sage: T
            VeeringTriangulation("(0,3,2)(1,~0,4)(5,6,~1)", "BRRBBBB")
            sage: L
            VeeringTriangulationLinearFamily("(0,3,2)(1,~0,4)(5,6,~1)", "BRRBBBB", [(1, 0, 0, 1, 1, 1, 1), (0, 1, 1, -1, -1, 1, 0)])

            sage: T.flip(5, 2)
            sage: L.flip(5, 2)
            sage: T
            VeeringTriangulation("(0,3,2)(1,~0,4)(5,~1,6)", "BRRBBBB")
            sage: L
            VeeringTriangulationLinearFamily("(0,3,2)(1,~0,4)(5,~1,6)", "BRRBBBB", [(1, 0, 0, 1, 1, 1, 1), (0, 1, 1, -1, -1, -1, 0)])
        """
        VeeringTriangulation.flip(self, e, col, Gx=self._subspace, check=check)
        self._subspace.echelonize()

    def flip_back(self, e, col, check=True):
        VeeringTriangulation.flip_back(self, e, col, Gx=self._subspace, check=check)
        self._subspace.echelonize()

    def geometric_polytope(self, x_low_bound=0, y_low_bound=0, hw_bound=0, backend='sage'):
        r"""
        Return the geometric polytope.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: T.geometric_polytope()
            A 4-dimensional polyhedron in QQ^6 defined as the convex hull of 1 point, 7 rays
            sage: T.as_linear_family().geometric_polytope(backend='ppl')
            A 4-dimensional polyhedron in QQ^6 defined as the convex hull of 1 point, 7 rays
            sage: T.as_linear_family().geometric_polytope(backend='sage')
            A 4-dimensional polyhedron in QQ^6 defined as the convex hull of 1 vertex and 7 rays

        An example in genus 2 involving a linear constraint::

            sage: vt, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(vt, [s, t])
            sage: PG = f.geometric_polytope(backend='ppl')
            sage: PG
            A 4-dimensional polyhedron in QQ^14 defined as the convex hull of 1 point, 7 rays
            sage: for r in PG.generators():
            ....:     if r.is_ray():
            ....:         print(r)
            ray(0, 1, 1, 1, 1, 1, 0, 2, 2, 2, 0, 0, 0, 2)
            ray(0, 1, 1, 1, 1, 1, 0, 2, 0, 0, 2, 2, 2, 2)
            ray(0, 2, 2, 2, 2, 2, 0, 1, 1, 1, 0, 0, 0, 1)
            ray(0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1)
            ray(2, 0, 0, 2, 2, 2, 2, 1, 1, 1, 0, 0, 0, 1)
            ray(1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1)
            ray(1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1)
        """
        ne = self._subspace.ncols()
        L = LinearExpressions(self.base_ring())
        x = [L.variable(i) for i in range(ne)]
        y = [L.variable(ne + i) for i in range(ne)]
        cs = ConstraintSystem()
        for i in range(ne):
            cs.insert(x[i] >= x_low_bound)
        for i in range(ne):
            cs.insert(y[i] >= y_low_bound)
        self._set_subspace_constraints(cs.insert, x, VERTICAL)
        self._set_subspace_constraints(cs.insert, y, HORIZONTAL)
        self._set_geometric_constraints(cs.insert, x, y, hw_bound=hw_bound)
        return polyhedron(cs, backend)

    def geometric_flips(self, backend='ppl'):
        r"""
        Return the list of geometric flips.

        A flip is geometric if it arises generically as a flip of L^oo-Delaunay
        triangulations along Teichmueller geodesics. These correspond to a subset
        of facets of the geometric polytope.

        OUTPUT: a list of pairs (edge number, new colour)

        EXAMPLES:

        L-shaped square tiled surface with 3 squares (given as a sphere with
        3 triangles). It has two geometric neighbors corresponding to simultaneous
        flipping of the diagonals 3, 4 and 5::

            sage: from veerer import *
            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(T, [s, t])
            sage: sorted(T.geometric_flips(backend='ppl'))
            [[(3, 1), (4, 1), (5, 1)], [(3, 2), (4, 2), (5, 2)]]
            sage: sorted(T.geometric_flips(backend='sage'))
            [[(3, 1), (4, 1), (5, 1)], [(3, 2), (4, 2), (5, 2)]]

        To be compared with the geometric flips in the ambient stratum::

            sage: sorted(T.as_linear_family().geometric_flips())
            [[(3, 1)], [(3, 2)], [(4, 1)], [(4, 2)], [(5, 1)], [(5, 2)]]

        A more complicated example::

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(2, 3, 5, 2, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(T, [s, t])
            sage: sorted(f.geometric_flips(backend='ppl'))
            [[(4, 2)], [(5, 1)], [(5, 2)]]
            sage: sorted(f.geometric_flips(backend='sage'))
            [[(4, 2)], [(5, 1)], [(5, 2)]]

        TESTS::

            sage: from veerer import VeeringTriangulation
            sage: fp = "(0,~8,~7)(1,3,~2)(2,7,~3)(4,6,~5)(5,8,~6)(~4,~1,~0)"
            sage: cols = "RBRRRRBBR"
            sage: vt = VeeringTriangulation(fp, cols)
            sage: sorted(vt.geometric_flips())
            [[(2, 1)], [(2, 2)], [(4, 1), (8, 1)], [(4, 2), (8, 2)]]
            sage: sorted(vt.as_linear_family().geometric_flips())
            [[(2, 1)], [(2, 2)], [(4, 1), (8, 1)], [(4, 2), (8, 2)]]
        """
        dim = self._subspace.nrows()
        ne = ambient_dim = self._subspace.ncols()
        L = LinearExpressions(self.base_ring())
        x = [L.variable(e) for e in range(ne)]
        y = [L.variable(ne + e) for e in range(ne)]
        P = self.geometric_polytope(backend=backend)
        if polyhedron_dimension(P, backend) != 2 * dim:
            raise ValueError('not geometric P.dimension() = {} while 2 * dim = {}'.format(P.dimension(), 2 * dim))

        delaunay_facets = collections.defaultdict(list)
        for e in self.forward_flippable_edges():
            a, b, c, d = self.square_about_edge(e)

            constraint = x[self._norm(e)] == y[self._norm(a)] + y[self._norm(d)]
            Q = polyhedron_add_constraints(P, constraint, backend)
            facet_dim = polyhedron_dimension(Q, backend)
            assert facet_dim < 2 * dim
            if facet_dim == 2*dim - 1:
                hQ = polyhedron_to_hashable(Q, backend)
                if hQ not in delaunay_facets:
                    delaunay_facets[hQ] = [Q, []]
                delaunay_facets[hQ][1].append(e)

        neighbours = []
        for Q, edges in delaunay_facets.values():
            for cols in itertools.product([BLUE, RED], repeat=len(edges)):
                Z = list(zip(edges, cols))
                cs = ConstraintSystem()
                for e, col in Z:
                    a, b, c, d = self.square_about_edge(e)
                    if col == RED:
                        cs.insert(x[self._norm(a)] <= x[self._norm(d)])
                    else:
                        cs.insert(x[self._norm(a)] >= x[self._norm(d)])
                S = polyhedron_add_constraints(Q, cs, backend)
                if polyhedron_dimension(S, backend) == 2 * dim - 1:
                    neighbours.append(Z)

        return neighbours



class VeeringTriangulationLinearFamilies:
    r"""
    A collection of linear families.
    """
    @staticmethod
    def L_shaped_surface(a1, a2, b1, b2, t1=0, t2=0):
        vt, s, t = VeeringTriangulations.L_shaped_surface(a1, a2, b1, b2, t1, t2)
        return VeeringTriangulationLinearFamily(vt, matrix([s, t]))
