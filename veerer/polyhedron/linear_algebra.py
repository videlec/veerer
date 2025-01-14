r"""
We are given a subspace as a matrix kernel of full rank
in echelon form (each row is a linear form).

Now we want to project a linear form to this subspace:
      just want to subtract the pivots
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2023 Vincent Delecroix
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


from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ

from sage.sets.disjoint_set import DisjointSet
from sage.rings.integer import GCD_list
from sage.arith.functions import LCM_list


def linear_form_project(equations, linear_form):
    r"""
    Put ``linear_form`` in a canonical way on the subspace defined by ``equations``.

    EXAMPLES::

        sage: from veerer.polyhedron.linear_algebra import linear_form_project  # random output due to deprecation warnings in realalg
        sage: equations = matrix(ZZ, [[3, -1, 0], [0, 0, 2]])
        sage: linear_form_project(equations, [1, 1, 1])
        [0, 4/3, 0]
        sage: linear_form_project(equations, [1, -1, 7])
        [0, -2/3, 0]
    """
    dim = equations.ncols()
    ef = equations.echelon_form()  # NOTE: this is cached
    pivots = equations.pivots()    # NOTE: this is cached
    for i, j in enumerate(equations.pivots()):
        if linear_form[j]:
            coeff = linear_form[j] / ef[i, j]
            for k in range(dim):
                linear_form[k] -= coeff * ef[i, k]
    return linear_form

def linear_form_normalize(base_ring, linear_form):
    r"""
    Normalize ``linear_form``.

    EXAMPLES::

        sage: from veerer.polyhedron.linear_algebra import linear_form_normalize
        sage: linear_form_normalize(ZZ, [-2, 0, 6])
        [1, 0, -3]
        sage: linear_form_normalize(ZZ, [0, 1])
        [0, 1]
    """
    dim = len(linear_form)
    if not any(linear_form):
        return
    if base_ring is ZZ or base_ring is QQ:
        # make it integral
        d = LCM_list([x.denominator() for x in linear_form])
        if not d.is_one():
            for k in range(dim):
                linear_form[k] = ZZ(d * linear_form[k])
        # remove gcd
        g = GCD_list(list(linear_form))
        if not g.is_one():
            for k in range(dim):
                linear_form[k] //= g
        # set sign
        i = 0
        while not linear_form[i]:
            i += 1
        if linear_form[i] < 0:
            for k in range(i, dim):
                linear_form[k] *= -1
    else:
        i = 0
        while not linear_form[i]:
            i += 1
        if not linear_form[i].is_one():
            c = linear_form[i]
            linear_form[i] = base_ring.one()
            for k in range(i + 1, dim):
                linear_form[k] /= c

    return linear_form


vector_normalize = linear_form_normalize


def prime_decomposition(mat, partition=None):
    r"""
    Return the prime decomposition of the matrix ``mat`` together with dimensions.

    EXAMPLES::

        sage: from veerer.polyhedron.linear_algebra import prime_decomposition
        sage: prime_decomposition(matrix(ZZ, 2, 3, [1, 0, 1, 0, 1, 0]))
        [([0, 2], [1 1]), ([1], [1])]

        sage: B = (ZZ**8).basis()
        sage: m = matrix([B[0] + B[1] + B[2], B[1] - B[2], B[3] + B[4] + B[5], B[6] + B[7]])
        sage: p0 = prime_decomposition(m)
        sage: p0
        [(
                   [ 1  0  2]
        [0, 1, 2], [ 0  1 -1]
        ),
         ([3, 4, 5], [1 1 1]),
         ([6, 7], [1 1])]
        sage: r = random_matrix(ZZ, 4, algorithm="unimodular")
        sage: m = r * m
        sage: p1 = prime_decomposition(m)
        sage: assert p1 == p0, (p1, p0, r)

    Column permutations (be careful that permutations in sage act on {1, ..., n})::

        sage: s = SymmetricGroup(6).random_element()
        sage: sinv = ~s
        sage: m.permute_columns(s)
        sage: p1 = prime_decomposition(m)
        sage: p2 = sorted((sorted(sinv(i + 1) - 1 for i in atom), dim) for atom, dim in p0)
        sage: assert [(atom, subspace.nrows()) for atom, subspace in p1] == [(atom, subspace.nrows()) for atom, subspace in p2]
    """
    mat = mat.echelon_form()
    if partition is None:
        partition = DisjointSet(mat.ncols())
    pivots = [None] * mat.ncols()
    for i, r in enumerate(mat.rows()):
        z = r.nonzero_positions()
        if not z:
            break
        for j in range(1, len(z)):
            partition.union(z[0], z[j])
        pivots[z[0]] = i
    gens = []
    for atom in partition:
        rows = [pivots[j] for j in atom if pivots[j] is not None]
        gens.append(mat.matrix_from_rows_and_columns(rows, atom))

    return list(zip(partition, gens))


def is_rank_one(m, ratios=False):
    r"""
    Return whether the given matrix ``m`` has rank one.

    If ``ratios`` is set to ``True`` then return a pair ``(ans,
    row_or_col_ratios)``

    EXAMPLES::

        sage: from veerer.polyhedron.linear_algebra import is_rank_one
        sage: assert is_rank_one(matrix(2, 2, [1, 1, 1, 1]))
        sage: assert is_rank_one(matrix(2, 3, [1, 1, 0, 2, 2, 0]))
        sage: assert not is_rank_one(matrix(2, 2, [1, 2, 1, 1]))
        sage: assert not is_rank_one(matrix(2, 2, [1, 1, 1, 2]))

        sage: is_rank_one(matrix(2, 2, [1, 1, 1, 1]), ratios=True)
        (True, [1, 1])
        sage: is_rank_one(matrix(2, 3, [1, 1, 0, 2, 2, 0]), ratios=True)
        (True, [1, 2])
    """
    if not m:
        raise ValueError("zero matrix")
    coeffs = []
    i0 = 0
    while not m[i0]:
        i0 += 1
        coeffs.append(0)
    j0 = 0
    while not m[i0, j0]:
        j0 += 1
    i = i0 + 1
    coeffs.append(1)
    for i in range(i0 + 1, m.nrows()):
        coeff = m[i, j0] / m[i0, j0]
        for j in range(m.ncols()):
            if m[i, j] != coeff * m[i0, j]:
                return (False, None) if ratios else False
        coeffs.append(coeff)
    return (True, coeffs) if ratios else True
