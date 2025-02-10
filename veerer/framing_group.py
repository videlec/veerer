r"""
Framing group
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024 Vincent Delecroix
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

import numbers
import array
import itertools

from sage.misc.cachefunc import cached_method
from sage.misc.misc_c import prod
from sage.categories.groups import Groups
from sage.structure.richcmp import op_LT, op_LE, op_EQ, op_NE, op_GT, op_GE, rich_to_bool
from sage.structure.element import Element, parent
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.integer_ring import ZZ
from sage.groups.libgap_wrapper import ElementLibGAP, ParentLibGAP
from sage.libs.gap.libgap import libgap
from sage.arith.functions import lcm
from sage.arith.misc import gcd
from sage.functions.other import factorial
from sage.groups.perm_gps.permgroup import PermutationGroup
from sage.groups.perm_gps.permgroup_named import SymmetricGroup

from veerer.permutation import perm_cycles, perm_id, perm_init, str_to_cycles_and_data, perm_compose, perm_check, perm_invert, perm_is_one


def runs(l):
    r"""
    EXAMPLES::

        sage: from veerer.framing_group import runs
        sage: list(runs([0, 0, 1, 1, 1, 2, 1]))
        [(0, 2), (1, 3), (2, 1), (1, 1)]
    """
    if isinstance(l, (tuple, list)):
        i = 0
        while i < len(l):
            j0 = i
            j = i + 1
            while j < len(l) and l[j0] == l[j]:
                j += 1
            yield (l[j0], j - j0)
            i = j
    elif isinstance(l, dict):
        for i in sorted(l, reverse=True):
            yield i, l[i]
    else:
        raise TypeError


# TODO: in order to handle multiscale monodromy, it would be convenient to be able to consider
# any (permutation) group obtained by the following operations
# basic blocks: cyclic groups Ck
# direct products: G1 x G2
# wreath products: G wreath Sym(n)
class FramingGroupElement(Element):
    r"""
    Holds two attributes ``p`` (a permutation) and ``r`` (an array)
    """
    def __init__(self, parent, p, r=None, check=True):
        self._p = p  # list of length n (permutation for each factor)
        if r is None:
            self._r = array.array('i', [0] * parent._n)
        else:
            self._r = r

        Element.__init__(self, parent)

        if check:
            # TODO: check that the permutation preserves the blocks
            self._check()

    def _check(self):
        P = self.parent()

        if not perm_check(self._p, P._n):
            raise ValueError("wrong p={}".format(self._p))

        if not isinstance(self._r, array.array) or self._r.typecode != 'i' or len(self._r) != P._n:
            raise ValueError("wrong r={}".format(self._r))

        # check that we stay in blocks
        j = 0
        block_start = 0
        block_end = P._multiplicities[0]
        A = P._angles[0]
        for x, (y, a) in enumerate(zip(self._p, self._r)):
            if x == block_end:
                j += 1
                if j < P._n:
                    block_start, block_end = block_end, block_end + P._multiplicities[j]
            assert block_start <= x < block_end
            if y < block_start or y >= block_end:
                raise ValueError("permutation does not preserve blocks")
            if a < 0 or a >= P._angles_flat[x]:
                raise ValueError("angle out of range a={} at x={}".format(a, x))

    def __call__(self, i, a=None):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([1,3],[2,3])
            sage: g = G("(0,1)(2:1,3:2,4:0)")
            sage: g(0, 0)
            (1, 0)
            sage: g(2, 0)
            (3, 1)
            sage: g(2, 1)
            (3, 2)
            sage: g(3, 0)
            (4, 2)
        """
        if not isinstance(i, numbers.Integral):
            raise TypeError
        P = self.parent()
        i = int(i)
        if i < 0 or i >= P._n:
            raise ValueError("index out of range")
        if a is not None:
            if not isinstance(a, numbers.Integral):
                raise TypeError
            return (self._p[i], (a + self._r[i]) % P._angles_flat[i])
        return self._p[i]

    def _richcmp_(self, other, op):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([1,3],[2,3])
            sage: for i, g in enumerate(G):
            ....:     for j, h in enumerate(G):
            ....:         assert (g == h) == (i == j)
            ....:         assert (g != h) == (i != j)
        """
        if op == op_EQ:
            return self._p == other._p and self._r == other._r
        elif op == op_NE:
            return self._p != other._p or self._r != other._r
        raise NotImplementedError

    def __hash__(self):
        x = 140737488617563
        x = ((x ^ hash(self._p.tobytes())) * 2147483693) + 82520 + len(self._p)
        x = ((x ^ hash(self._r.tobytes())) * 2147483693) + 82520 + len(self._r)
        return x

    def is_one(self):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([0,1,2,3], [2,1,3,2])
            sage: [g for g in G if g.is_one()]
            [()]
        """
        P = self.parent()
        return perm_is_one(self._p, P._n) and not any(self._r)

    def __invert__(self):
        P = self.parent()
        p = perm_invert(self._p, P._n)
        r = array.array('i', [-1] * P._n)
        for i in range(P._n):
            r[i] = (-self._r[p[i]]) % P._angles_flat[i]
        return P.element_class(P, p, r)

    def _mul_(self, other):
        r"""
        TESTS::

            sage: from veerer.framing_group import FramingGroup

            sage: G = FramingGroup([0,1,2,3], [2,1,3,2])
            sage: a = G("(3:0, 4:0, 5:0)")
            sage: b = G("(6:0, 7:0)")
            sage: c = G("(3:1,4:1,5:1)(6:2,7:1)")
            sage: d = G("(0:0,1:0)(3:1)(4:1)")
            sage: assert (a * b) * (c * d) == (a * (b * c)) * d == a * ((b * c) * d) == ((a * b) * c) * d == (a * (b * (c * d))) == (a * b) * (c * d)

            sage: G = FramingGroup([0,1,2,3], [2,1,3,2])
            sage: gens = G.gens()
            sage: todo = list(gens)
            sage: elts = set(todo)
            sage: while todo:
            ....:     g = todo.pop()
            ....:     for h in gens:
            ....:         hh = h * g
            ....:         if hh not in elts:
            ....:             elts.add(hh)
            ....:             todo.append(hh)
            sage: assert len(elts) == G.cardinality() == 1728
        """
        P = self.parent()
        p = perm_compose(self._p, other._p, P._n)
        r = array.array('i', [-1] * P._n)
        for i in range(P._n):
            r[i] = (self._r[i] + other._r[self._p[i]]) % P._angles_flat[i]
        return P.element_class(P, p, r)

    def permutation(self):
        r"""
        Return the permutation representative.

        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([3,4], [4,4])
            sage: g = G("(0:0,1:1,3:0)(4:2,6:1,5:1,7:1)")
            sage: g.permutation()
            array('i', [3, 4, 5, 10, 11, 9, 6, 7, 8, 0, 1, 2, 22, 23, 20, 21, 25, 26, 27, 24, 17, 18, 19, 16, 13, 14, 15, 12])
            sage: G.from_permutation(g.permutation()) == g
            True

            sage: g = G("(0:3)(1:2,2:0)(5:0,7:1)")
            sage: G.from_permutation(g.permutation()) == g
            True
        """
        P = self.parent()
        p = array.array('i', [-1] * sum(a * m for a, m in zip(P._angles, P._multiplicities)))
        i = 0
        j = 0
        for a, m in zip(P._angles, P._multiplicities):
            for ii in range(i, i + m):
                for jj in range(a):
                    p[j + a * (ii - i) + jj] = j + a * (self._p[ii] - i) + (jj + self._r[ii]) % a
            i += m
            j += a * m
        return p

    def symmetric_group_element(self):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([3,4], [4,4])
            sage: g1 = G("(0:0,1:1,3:0)(4:2,6:1,5:1,7:1)")
            sage: g1.symmetric_group_element()
            (1,4,11,2,5,12,3,6,10)(13,23,20,25,14,24,17,26,15,21,18,27,16,22,19,28)
            sage: G.from_symmetric_group_element(g1.symmetric_group_element()) == g1
            True

            sage: g2 = G("(0:3)(1:2,2:0)(5:0,7:1)")
            sage: g2.symmetric_group_element()
            (4,9,6,8,5,7)(17,25,18,26,19,27,20,28)
            sage: G.from_symmetric_group_element(g2.symmetric_group_element()) == g2
            True

            sage: assert (~g1).symmetric_group_element() == ~(g1.symmetric_group_element())
            sage: assert (~g2).symmetric_group_element() == ~(g2.symmetric_group_element())
            sage: (g1 * g2 * ~g1).symmetric_group_element() == (g1.symmetric_group_element() * g2.symmetric_group_element() * (~g1).symmetric_group_element())
            True
        """
        return self.parent().symmetric_group()([i + 1 for i in self.permutation()])

    def cycle_string(self, singletons=False):
        s = []
        for cyc in perm_cycles(self._p, True, self.parent()._n):
            if singletons or len(cyc) != 1 or self._r[cyc[0]] != 0:
                c = ", ".join("{}:{}".format(j, self._r[j]) for j in cyc)
                s.append("(" + c + ")")
        return "()" if not s else "".join(s)

    def _repr_(self):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([2], [2])
            sage: G([1,0])
            (0:0, 1:0)
            sage: G([1,0], [1,0])
            (0:1, 1:0)
            sage: G([1,0], [0,1])
            (0:0, 1:1)
            sage: G([1,0], [1,1])
            (0:1, 1:1)
        """
        return self.cycle_string()

    def order(self):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: from veerer.permutation import perm_order
            sage: G = FramingGroup([2], [2])
            sage: for g in G:
            ....:     print(g, g.order(), perm_order(g.permutation()))
            () 1 1
            (1:1) 2 2
            (0:1) 2 2
            (0:1)(1:1) 2 2
            (0:0, 1:0) 2 2
            (0:0, 1:1) 4 4
            (0:1, 1:0) 4 4
            (0:1, 1:1) 2 2
        """
        P = self.parent()
        o = ZZ.one()
        for cyc in perm_cycles(self._p, True, P._n):
            a = P._angles_flat[cyc[0]]
            o = lcm(o, len(cyc) * a // gcd(sum(self._r[j] for j in cyc), a))
        return o


class FramingGroup(Parent, UniqueRepresentation):
    r"""
    A product of wreath products of cyclic group.

    EXAMPLES::

        sage: from veerer.framing_group import FramingGroup
        sage: FramingGroup([1]).cardinality()
        1
        sage: FramingGroup([1, 1]).cardinality()
        2
        sage: FramingGroup([1, 1, 1]).cardinality()
        6
        sage: FramingGroup([3]).cardinality()
        3
        sage: FramingGroup([2, 2, 2, 2]).cardinality()
        384
        sage: FramingGroup([3] * 4 + [0] * 4).cardinality()
        46656
        sage: factorial(4) * 3**4 * factorial(4)
        46656
    """
    Element = FramingGroupElement

    @staticmethod
    def __classcall_private__(cls, angles, multiplicities=None):
        if multiplicities is None:
            if isinstance(angles, dict):
                it = angles.items()
            elif isinstance(angles, (tuple, list)):
                if not angles or isinstance(angles[0], (tuple, list)) and len(angles[0]) == 2:
                    it = angles
                else:
                    it = runs(angles)
            else:
                raise TypeError
        else:
            it = zip(angles, multiplicities)

        clean_angles = []
        clean_multiplicities = []
        for a, m in it:
            if not isinstance(a, numbers.Integral) or a < 0 or not isinstance(m, numbers.Integral) or m <= 0:
                raise ValueError
            clean_angles.append(max(1, int(a)))
            clean_multiplicities.append(int(m))

        return super().__classcall__(cls, tuple(clean_angles), tuple(clean_multiplicities))

    def __init__(self, angles, multiplicities):
        self._angles = angles
        self._multiplicities = multiplicities
        self._n = sum(self._multiplicities)
        self._angles_flat = []

        for a, m in zip(self._angles, self._multiplicities):
            self._angles_flat.extend([a] * m)

        Parent.__init__(self, category=Groups().Finite())

    def _repr_(self):
        return "FramingGroup({})".format(", ".join("%d^%d" %(a, m) if m > 1 else "%d" % a for a, m in zip(self._angles, self._multiplicities)))

    @cached_method
    def symmetric_group(self):
        return SymmetricGroup(sum(m * a for a, m in zip(self._angles, self._multiplicities)))

    def gens(self):
        r"""
        Return a generating set of this framing group.

        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: FramingGroup([0], [1]).gens()
            [()]
            sage: FramingGroup([0], [2]).gens()
            [(0:0, 1:0)]
            sage: FramingGroup([0], [3]).gens()
            [(0:0, 1:0), (0:0, 1:0, 2:0)]

            sage: FramingGroup([1], [1]).gens()
            [()]
            sage: FramingGroup([1], [2]).gens()
            [(0:0, 1:0)]
            sage: FramingGroup([1], [3]).gens()
            [(0:0, 1:0), (0:0, 1:0, 2:0)]

            sage: FramingGroup([2], [1]).gens()
            [(0:1)]
            sage: FramingGroup([2], [2]).gens()
            [(0:1), (0:0, 1:0)]
            sage: FramingGroup([2], [3]).gens()
            [(0:1), (0:0, 1:0), (0:0, 1:0, 2:0)]

            sage: FramingGroup([0,1,2,3], [2,1,3,2]).gens()
            [(0:0, 1:0), (3:1), (3:0, 4:0), (3:0, 4:0, 5:0), (6:1), (6:0, 7:0)]
        """
        ans = []
        i = 0
        for a, m in zip(self._angles, self._multiplicities):
            if m == 1 and a <= 1:
                i += 1
                continue

            if a >= 2:
                p = perm_id(self._n)
                r = array.array('i', [0] * i + [1] + [0] * (self._n - i - 1))
                ans.append(self(p, r))

            if m == 1:
                i += 1
                continue

            p = array.array('i', list(range(i)) + [i + 1, i] + list(range(i + 2, self._n)))
            ans.append(self(p))

            if m >= 3:
                p = array.array('i', list(range(i)) + list(range(i + 1, i + m)) + [i] + list(range(i + m, self._n)))
                ans.append(self(p))

            i += m

        return [self.one()] if not ans else ans

    def _element_constructor_(self, p, r=None):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([2, 3], [3, 3])
            sage: G("(0:1,2:0,1:10)")
            (0:1, 2:0, 1:0)
            sage: G([2,1,0,5,4,3], [1,10,3,0,1,0])
            (0:1, 2:1)(3:0, 5:0)(4:1)
        """
        if isinstance(p, str):
            if r is None:
                p, r = str_to_cycles_and_data(p)
                p = perm_init(p, self._n)
                r = array.array('i', [r.get(i, 0) for i in range(self._n)])
                for i in range(self._n):
                    r[i] = r[i] % self._angles_flat[i]
            else:
                p = perm_init(p, self._n)
        elif isinstance(p, (tuple, list)):
            p = perm_init(p, self._n)
        elif not p or p == 1:
            return self.one()

        if isinstance(r, (tuple, list)):
            r = array.array('i', [x % a for x, a in zip(r, self._angles_flat)])

        return self.element_class(self, p, r)

    @cached_method
    def one(self):
       return self.element_class(self, perm_id(self._n), array.array('i', [0] * self._n))

    @cached_method
    def rotation(self):
        r"""
        Return the element which corresponds to add +1 in each factor.

        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: FramingGroup([2, 2]).rotation()
            (0:1)(1:1)
            sage: FramingGroup([2, 2]).rotation().order()
            2

            sage: FramingGroup([1,2,3], [1,3,1]).rotation()
            (1:1)(2:1)(3:1)(4:1)
            sage: FramingGroup([1,2,3], [1,3,1]).rotation().order()
            6
        """
        return self.element_class(self, perm_id(self._n), array.array('i', [1 % a for a in self._angles_flat]))

    def from_permutation(self, q):
        r"""
        Build an element of this framing group from a "flat" permutation.
        """
        if not perm_check(q, sum(a * m for a, m in zip(self._angles, self._multiplicities))):
           raise ValueError("invalid input q")
        i = 0
        j = 0
        p = array.array('i', [-1] * self._n)
        r = array.array('i', [-1] * self._n)
        for a, m in zip(self._angles, self._multiplicities):
            for ii in range(i, i + m):
                for jj in range(a):
                    im = q[j + a * (ii - i) + jj]

                    x = (im - j) % a   # (jj + self._r[ii])
                    xx = (x - jj) % a
                    if xx >= a:
                        raise ValueError("invalid")
                    if r[ii] == -1:
                        r[ii] = xx
                    elif r[ii] != xx:
                        raise ValueError("invalid input")

                    x = (im - j) // a  # (self._p[ii] - i)
                    if x < 0 or x >= m:
                        raise ValueError("invalid input")
                    if p[ii] == -1:
                        p[ii] = i + x
                    elif p[ii] != i + x:
                        raise ValueError("invalid input")
            i += m
            j += a * m
        return self.element_class(self, p, r)

    def from_symmetric_group_element(self, q):
        S = self.symmetric_group()
        if q not in S:
            raise ValueError
        return self.from_permutation(array.array('i', [i - 1 for i in S(q).domain()]))

    def __iter__(self):
        r"""
        TESTS::

            sage: from veerer.framing_group import FramingGroup
            sage: list(FramingGroup([2], [2]))
            [(), (1:1), (0:1), (0:1)(1:1), (0:0, 1:0), (0:0, 1:1), (0:1, 1:0), (0:1, 1:1)]
        """
        i = 0
        perm_blocks = []
        for a, m in zip(self._angles, self._multiplicities):
            perm_blocks.append(itertools.permutations(range(i, i + m)))
            i += m
        for p in itertools.product(*perm_blocks):
            p = array.array('i', sum(p, ()))
            angle_blocks = []
            for a, m in zip(self._angles, self._multiplicities):
                angle_blocks.append(itertools.product(range(a), repeat=m))
                i += m
            for r in itertools.product(*angle_blocks):
                r = array.array('i', sum(r, ()))
                yield self.element_class(self, p, r, check=True)

    def cardinality(self):
        r"""
        TESTS::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([2], [2])
            sage: libgap(G).Size() == G.cardinality()
            True
            sage: G = FramingGroup([0,1,2,3], [1,3,4,1])
            sage: libgap(G).Size() == G.cardinality()
            True
        """
        return prod(ZZ(m).factorial() * ZZ(a) ** m for a, m in zip(self._angles, self._multiplicities))

    def subgroup(self, gens=None, mutable=False):
        return FramingSubgroup(self, gens, mutable)

    def _libgap_(self):
        # the underlying group is a direct product of separatrix permutation
        # of zeros/poles of fixed degree. For each degree we either consider
        # * ignore it if there is a single choice
        # * a symmetric group if there is <= 1 separatrix
        # * a cyclic group if the multiplicity is one
        # * a wreath product otherwise
        try:
            return self._libgap
        except AttributeError:
            pass
        from sage.libs.gap.libgap import libgap
        components = []
        for a, m in zip(self._angles, self._multiplicities):
            if a == 1 and m == 1:
                continue
            if a == 1:
                components.append(libgap.SymmetricGroup(m))
            elif m == 1:
                components.append(libgap.CyclicGroup(a))
            else:
                G = libgap.CyclicGroup(a)
                H = libgap.SymmetricGroup(m)
                components.append(libgap.WreathProduct(G, H))
        if not components:
            self._libgap = libgap.TrivialGroup()
        else:
            self._libgap = libgap.DirectProduct(components)
        return self._libgap


class FramingSubgroup(Parent):
    r"""
    EXAMPLES::

        sage: from veerer.framing_group import FramingGroup
        sage: G = FramingGroup([1, 2, 3], [5, 3, 4])
        sage: g1 = G("(0:1,4:2)(5:0,6:1)(7:2)(9:1,10:1)")
        sage: g2 = G("(0:0,1:0,2:0,3:0)")
        sage: H = G.subgroup([g1, g2], mutable=True)
        sage: H
        FramingSubgroup([(0:0, 4:0)(5:0, 6:1)(9:1, 10:1), (0:0, 1:0, 2:0, 3:0)])
        sage: H.index()
        7776
        sage: assert g1 in H and g2 in H and (g1 * g2) in H
        sage: g3 = G("(5:0,7:0)")
        sage: H.add_generator(g3)
        sage: assert (g1 * g3 * g2) in H
        sage: H.index()
        648
        sage: g4 = G("(8:0,10:0,11:0,9:0)")
        sage: H.add_generator(g4)
        sage: assert (g1 * g3 * g4) in H
        sage: H.index()
        54
    """
    def __init__(self, ambient_group, gens=None, mutable=False):
        self._ambient_group = ambient_group
        self._mutable = True
        self._generators = []
        Parent.__init__(self, category=Groups().Finite(), facade=self._ambient_group)
        if gens is not None:
            for g in gens:
                self.add_generator(g)
        self._mutable = mutable

    def gens(self):
        r"""
        Return generators of this framing subgroup.
        """
        return tuple(self._generators)

    def _element_constructor_(self, *args, **kwds):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: f = VeeringTriangulationLinearFamily("(0:1)(~0:1,1:1,2:1,~1:1)(~2:1)", "RBR", [(1, 0, 1), (0, 1, 0)])
            sage: ds_graph = f.delaunay_strebel_graph()
            sage: G = ds_graph.framing_group()
            sage: G("(0:1)(1:1)(2:1)")
            (0:1)(1:1)(2:1)
            sage: G("(0:1)(1:1)")
            Traceback (most recent call last):
            ...
            ValueError: not an element of this framing group subgroup
        """
        g = self._ambient_group(*args, **kwds)
        if g not in self:
            raise ValueError("not an element of this framing group subgroup")
        return g

    def set_immutable(self):
        self._mutable = False

    def _repr_(self):
        return "FramingSubgroup({})".format(self._generators)

    def __contains__(self, g):
        return parent(g) is self._ambient_group and g.symmetric_group_element() in self.permutation_group()

    def __le__(self, other):
        r"""
        Test whether self is a subgroup of other
        """
        if isinstance(self, FramingSubgroup) and isinstance(other, FramingSubgroup):
            if self._ambient_group != other._ambient_group:
                raise TypeError

        elif isinstance(self, FramingGroup):
            if other._ambient_group != self:
                raise TypeError

        elif isinstance(other, FramingGroup):
            if self._ambient_group != other:
                raise TypeError

            return True

        else:
            return NotImplemented

        for g in self.gens():
            if g not in other:
                return False

        return True

    def __eq__(self, other):
        if type(self) is type(other) or (isinstance(self, (FramingGroup, FramingSubgroup)) and isinstance(other, (FramingGroup, FramingSubgroup))):
            return self <= other and other <= self

        return NotImplemented

    def __ne__(self, other):
        return not (self == other)

    def __gt__(self, other):
        return not (self <= other)

    def __lt__(self, other):
        return (self <= other) and not (other <= self)

    def __ge__(self, other):
        return other <= self

    def copy(self, mutable=None):
        if mutable is None:
            mutable = self._mutable
        if not mutable and not self._mutable:
            return self
        F = FramingSubgroup(self._ambient_group)
        F._generators = self._generators[:]
        F._mutable = mutable
        return F

    def permutation_group(self):
        try:
            return self._permutation_group
        except AttributeError:
            pass

        permutation_group = PermutationGroup([g.symmetric_group_element() for g in self._generators])

        if not self._mutable:
            self._permutation_group = permutation_group
        return permutation_group

    def add_generator(self, g):
        if not self._mutable:
            raise ValueError("immutable framing subgroup; use a mutable copy instead")
        if parent(g) is not self._ambient_group:
            raise ValueError
        if g not in self:
            self._generators.append(g)

    def cardinality(self):
        return self.permutation_group().cardinality()

    def structure_description(self):
        return self.permutation_group().structure_description()

    __len__ = cardinality

    def index(self):
        return self._ambient_group.cardinality() // self.cardinality()

    def __iter__(self):
        r"""
        EXAMPLES::

            sage: from veerer.framing_group import FramingGroup
            sage: G = FramingGroup([1, 2, 3], [2, 2, 2])
            sage: g1 = G("(0:0,1:0)(2:0,3:0)(4:0,5:0)")
            sage: g2 = G("(0:1)(2:1)(4:1)")
            sage: assert all(g in G for g in G)
            sage: sum(1 for _ in G.subgroup([g1, g2]))
            72
        """
        yield from (self._ambient_group.from_symmetric_group_element(g) for g in self.permutation_group())
