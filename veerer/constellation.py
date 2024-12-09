r"""
Constellations (possibly with boundary data)

Common base claas for class:~veerer.triangulation.Triangulations and :class:~veerer.strebel_graph.StrebelGraph
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2018 Mark Bell
#                     2018-2024 Vincent Delecroix
#                     2024 Kai Fu
#                     2018 Saul Schleimer
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

import collections
import numbers
from array import array

from sage.structure.richcmp import op_LT, op_LE, op_EQ, op_NE, op_GT, op_GE, rich_to_bool

from .permutation import (perm_init, perm_check, perm_cycles,
                          perm_invert, perm_conjugate, perm_cycle_string, perm_cycles_lengths,
                          perm_cycles_to_string, perm_on_list, perm_on_edge_list, perm_cycle_type,
                          perm_num_cycles, str_to_cycles, str_to_cycles_and_data, perm_compose, perm_from_base64_str,
                          uint_base64_str, uint_from_base64_str, perm_base64_str,
                          perms_are_transitive, perms_orbits, edge_relabelling_from)


class Constellation:
    __slots__ = ['_mutable',  # mutability flag
                 '_ne',  # number of edges
                 '_vp',  # vertex permutation
                 '_fp',  # face permutation
                 '_half_edges_data',  # a list of half-edges data: each element is an array of length 2 * _ne
                 '_edges_data',  # a list of edges data: each element is an array of length _ne
                ]

    def __init__(self, ne, vp, fp, half_edges_data, edges_data, mutable=False, check=True):
        self._ne = ne

        if vp is None:
            vp = self._vp = array('i', [-1] * (2 * ne))
            for i in range(2 * ne):
                if fp[i] == -1:
                    continue
                ii = fp[i ^ 1 if fp[i ^ 1] != -1 else i]
                vp[ii] = i
        else:
            self._vp = vp

        self._fp = fp

        self._half_edges_data = half_edges_data
        self._edges_data = edges_data
        self._mutable = mutable
        self._set_data_pointers()

        if check:
            self._check(ValueError)

    def _ep(self, i):
        if self._vp[i] == -1:
            return -1
        elif self._vp[i ^ 1] == -1:
            return i
        else:
            return i ^ 1

    def _set_data_pointers(self):
        pass

    def _check(self, error=RuntimeError):
        ne = self._ne

        if not (hasattr(self, '_vp') and hasattr(self, '_fp') and hasattr(self, '_half_edges_data') and hasattr(self, '_edges_data')):
            raise error('missing attributes: these must be _vp, _ep, _fp, _data')
        if not perm_check(self._vp, 2 * ne):
            raise error('vp is not a permutation: {}'.format(self._vp))
        if not perm_check(self._fp, 2 * ne):
            raise error('fp is not a permutation: {}'.format(self._fp))

        for i in range(2 * ne):
            if (self._vp[i] == -1) != (self._fp[i] == -1):
                raise ValueError("vp and fp with different domains")

        for l in self._half_edges_data:
            if not isinstance(l, collections.abc.Sequence):
                raise error('each half-edges data must be a sequence of same length as the underlying permutations got a {}'.format(type(l).__name__))
            if len(l) != 2 * ne:
                raise error('half-edges data of wrong length: got a {} of length {}'.format(type(l).__name__, len(l)))
            if self._mutable and not isinstance(l, collections.abc.MutableSequence):
                raise error('immutable data in mutable object')

        for l in self._edges_data:
            if not isinstance(l, collections.abc.Sequence) or len(l) != ne:
                raise error('each edges data must be a sequence of length the number of edges; got a {} of length {}'.format(type(l).__name__, len(l)))
            if self._mutable and not isinstance(l, collections.abc.MutableSequence):
                raise error('immutable data in mutable object')

        for i in range(2 * ne):
            if self._vp[i] == -1:
                for l in self._half_edges_data:
                    if l[i]:
                        raise error('non-zero entry {} in half-edge data at the non-active half-edge {}'.format(l[i], i))
            elif self._fp[self._ep(self._vp[i])] != i:
                raise error('fev relation not satisfied at half-edge i={}'.format(self._half_edge_string(i)))

    def _check_alloc(self, n):
        if len(self._vp) < n or len(self._ep) < n or len(self._fp) < n:
            raise TypeError("reallocation needed")

    def _realloc(self, n_max):
        if n_max < self._n:
            return
        self._vp.extend([-1] * (n_max - self._n))
        self._ep.extend([-1] * (n_max - self._n))
        self._fp.extend([-1] * (n_max - self._n))

    def __getstate__(self):
        r"""
        TESTS::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph

            sage: t = Triangulation("(0,1,2)")
            sage: _ = dumps(t)  # indirect doctest
            sage: t = VeeringTriangulation("(0,1,2)", "BBR")
            sage: _ = dumps(t)  # indirect doctest
            sage: t = VeeringTriangulation("(0,1,2)(~0,3,4)", "(~1:1)(~2:1)(~3:1)(~4:1)", "RBRBR")
            sage: _ = dumps(t)  # indirect doctest
        """
        a = [self._ne]
        a.append(len(self._half_edges_data))
        a.append(len(self._edges_data))
        a.append(self._mutable)
        a.extend(self._fp)
        for l in self._half_edges_data:
            a.extend(l)
        for l in self._edges_data:
            a.extend(l)
        return a

    def __setstate__(self, arg):
        r"""
        TESTS::

            sage: from veerer import Triangulation
            sage: t0 = Triangulation("(0,1,2)", mutable=False)
            sage: t1 = Triangulation("(0,1,2)", mutable=True)
            sage: s0 = loads(dumps(t0))  # indirect doctest
            sage: assert s0 == t0 and s0._mutable is False
            sage: s0._check()
            sage: s1 = loads(dumps(t1))  # indirect doctest
            sage: assert s1 == t1 and s1._mutable is True
            sage: s1._check()

            sage: t0 = Triangulation("(0,1,2)(~0:1)(~1:1)", mutable=False)
            sage: t1 = Triangulation("(0,1,2)(~0:1)(~1:1)", mutable=True)
            sage: s0 = loads(dumps(t0))  # indirect doctest
            sage: assert s0 == t0 and s0._mutable is False
            sage: s0._check()
            sage: s1 = loads(dumps(t1))  # indirect doctest
            sage: assert s1 == t1 and s1._mutable is True
            sage: s1._check()

            sage: from veerer import VeeringTriangulation
            sage: t0 = VeeringTriangulation("(0,1,2)", "BBR", mutable=False)
            sage: t1 = VeeringTriangulation("(0,1,2)", "BBR", mutable=True)
            sage: t2 = VeeringTriangulation("(0,1,2)(~0,3,4)", "(~1:1)(~2:1)(~3:1)(~4:1)", "RBRBR")

            sage: s0 = loads(dumps(t0))  # indirect doctest
            sage: assert s0 == t0 and s0._mutable is False
            sage: s0._check()

            sage: s1 = loads(dumps(t1))  # indirect doctest
            sage: assert s1 == t1 and s1._mutable is True
            sage: s1._check()

            sage: s2 = loads(dumps(t2))
            sage: assert s2 == t2
        """
        # We do not know how many slots we have in data
        ne = self._ne = arg[0]
        n = 2 * ne
        k_half_edges = arg[1]  # length of half-edges data
        k_edges = arg[2]  # length of edges data
        self._mutable = arg[3]
        shift = 4
        self._fp = array('i', arg[shift : shift + n])
        shift += n

        half_edges_data = []
        for _ in range(k_half_edges):
            half_edges_data.append(array('i', arg[shift: shift + n]))
            shift += n
        edges_data = []
        for i in range(k_edges):
            edges_data.append(array('i', arg[shift: shift + ne]))
            shift += ne

        assert shift == len(arg)

        self._vp = array('i', [-1] * n)
        for i in range(n):
            if self._fp[i] == -1:
                continue
            ii = (i ^ 1) if self._fp[i ^ 1] != -1 else i
            self._vp[self._fp[ii]] = i

        self._half_edges_data = tuple(half_edges_data)
        self._edges_data = tuple(edges_data)
        self._set_data_pointers()

    def set_immutable(self):
        self._mutable = False

    def __hash__(self):
        r"""
        TESTS::

            sage: from itertools import permutations, combinations
            sage: from veerer import Triangulation, VeeringTriangulation

            sage: triangulations = []

            sage: t = Triangulation("(0, 1, 2)")
            sage: triangulations.append(t)

            sage: for p in permutations(["1", "~1", "2", "~2"]):
            ....:     t = Triangulation("(0, {}, {})(~0, {}, {})".format(*p))
            ....:     triangulations.append(t)

            sage: for i, j in combinations([0, 1, 2, 3], 2):
            ....:     for k, l in permutations(set(range(4)).difference([i, j])):
            ....:         vars = {'i': i, 'j': j, 'k': k, 'l': l}
            ....:         t = Triangulation("({i}, {j}, {k})(~{i}, ~{j}, {l})".format(**vars))
            ....:         triangulations.append(t)
            ....:         t = Triangulation("({i}, ~{j}, {k})(~{i}, {j}, {l})".format(**vars))
            ....:         triangulations.append(t)
            ....:         t = Triangulation("({i}, {k}, {j})(~{i}, ~{j}, {l})".format(**vars))
            ....:         triangulations.append(t)
            ....:         t = Triangulation("({i}, {k}, ~{j})(~{i}, {j}, {l})".format(**vars))
            ....:         triangulations.append(t)
            ....:         t = Triangulation("({i}, {j}, {k})(~{i}, {l}, ~{j})".format(**vars))
            ....:         triangulations.append(t)
            ....:         t = Triangulation("({i}, ~{j}, {k})(~{i}, {l}, {j})".format(**vars))
            ....:         triangulations.append(t)
            ....:         t = Triangulation("({i}, {k}, {j})(~{i}, {l}, ~{j})".format(**vars))
            ....:         triangulations.append(t)
            ....:         t = Triangulation("({i}, {k}, ~{j})(~{i}, {l}, {j})".format(**vars))
            ....:         triangulations.append(t)

            sage: for i in range(len(triangulations)):
            ....:     for j in range(len(triangulations)):
            ....:         assert (triangulations[i] == triangulations[j]) == (i == j), (i, j)
            ....:         assert (triangulations[i] != triangulations[j]) == (i != j), (i, j)

            sage: hashes = {}
            sage: for t in triangulations:
            ....:     h = hash(t)
            ....:     if h in hashes:
            ....:         print('collision: {} {}'.format(hashes[h], t))
            ....:     else:
            ....:         hashes[h] = t
            sage: assert len(hashes) == len(triangulations), (len(hashes), len(triangulations))

            sage: triangulations = []
            sage: for cols in ["RRB", "RBR", "BRR", "BBR", "BRB", "RBB"]:
            ....:     t = VeeringTriangulation("(0,1,2)", cols)
            ....:     triangulations.append(t)

            sage: for i in range(len(triangulations)):
            ....:     for j in range(len(triangulations)):
            ....:         assert (triangulations[i] == triangulations[j]) == (i == j), (i, j)
            ....:         assert (triangulations[i] != triangulations[j]) == (i != j), (i, j)

            sage: hashes1 = {}
            sage: hashes2 = {}
            sage: for t in triangulations:
            ....:     h1 = hash(t) % (2 ** 16)
            ....:     h2 = (hash(t) >> 16) % (2 ** 16)
            ....:     if h1 in hashes1:
            ....:         print('collision 1: {} {}'.format(hashes1[h1], t))
            ....:     else:
            ....:         hashes1[h1] = t
            ....:     if h2 in hashes2:
            ....:         print('collision 2: {} {}'.format(hashes2[h2], t))
            ....:     else:
            ....:         hashes2[h2] = t
            sage: assert len(hashes1) == len(hashes2) == len(triangulations), (len(hashes1), len(hashes2), len(triangulations))

            sage: t = VeeringTriangulation("(0,1,2)", cols, mutable=True)
            sage: hash(t)
            Traceback (most recent call last):
            ...
            ValueError: mutable veering triangulation not hashable
        """
        if self._mutable:
            raise ValueError('mutable veering triangulation not hashable')

        x = 140737488617563
        n = 2 * self._ne
        x = ((x ^ hash(self._vp.tobytes())) * 2147483693) + 82520 + n

        for l in self._half_edges_data:
            x = ((x ^ hash(l.tobytes())) * 2147483693) + 82520 + n
        for l in self._edges_data:
            x = ((x ^ hash(l.tobytes())) * 2147483693) + 82520 + n

        return x

    def _check_half_edge(self, h):
        if not isinstance(h, numbers.Integral):
            raise TypeError('invalid half-edge {}'.format(h))
        h = int(h)
        if h < 0 or h >= 2 * self._ne:
            raise ValueError('half-edge number out of range e={}'.format(e))
        if self._vp[h] == -1:
            raise ValueError("invalid half-edge h={}; the underlying edges is folded".format(h))
        return h

    def to_string(self):
        r"""
        Serialize this triangulation as a string.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph

            sage: Triangulation("(0,1,2)(~0,~1,~2)").to_string()
            '3_1___234501_000000'
            sage: Triangulation("(0,1,2)", boundary="(~0:1)(~1:1,~2:1)").to_string()
            '3_1___214503_010101'

            sage: VeeringTriangulation("(0,1,2)", "RRB").to_string()
            '3_1_1__2~4~0~_000000_112'

            sage: StrebelGraph("(0,1,2)(~0,~1:1,~2:2)").to_string()
            '3_1___234501_000102'
        """
        data = [uint_base64_str(self._ne),
                uint_base64_str(len(self._half_edges_data)),
                uint_base64_str(len(self._edges_data)),
                uint_base64_str(self._mutable),
                perm_base64_str(self._fp)]
        for l in self._half_edges_data:
            data.append(perm_base64_str(l))
        for l in self._edges_data:
            data.append(perm_base64_str(l))
        return '_'.join(data)

    @classmethod
    def from_permutations(cls, vp, fp, half_edges_data=(), edges_data=(), mutable=False, check=True):
        r"""
        INPUT:

        - ``vp``, ``ep``, ``fp`` -- the vertex, edge and face permutations

        - ``data``

        - ``check`` - boolean (default: ``True``) - if set to ``False`` no
          check are performed

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph
            sage: from array import array

            sage: vp = array('i', [4, 8, 1, 12, 3, -1, 0, -1, 6, -1, 2, -1, 10, -1])
            sage: fp = array('i', [2, 6, 4, 10, 0, -1, 8, -1, 1, -1, 12, -1, 3, -1])

            sage: Triangulation.from_permutations(vp, fp, (array('i', [0] * 14),))
            Triangulation("(0,1,2)(~0,3,4)(~1,5,6)")
            sage: Triangulation.from_permutations(vp, None, (array('i', [0] * 14),))
            Triangulation("(0,1,2)(~0,3,4)(~1,5,6)")
            sage: Triangulation.from_permutations(None, fp, (array('i', [0] * 14),))
            Triangulation("(0,1,2)(~0,3,4)(~1,5,6)")

            sage: vp = array('i', [2, 3, 1, 0])
            sage: StrebelGraph.from_permutations(vp, None, (array('i', [1, 1, 0, 0]),))
            StrebelGraph("(0:1,1,~0:1,~1)")
        """
        if (vp is None) and (fp is None):
            raise ValueError('at most one of vp or fp could be None')

        C = cls.__new__(cls)
        n = len(vp) if vp is not None else len(fp)
        if n % 2:
            raise ValueError("permutations must be even length")

        if vp is None:
            vp = array('i', [-1] * n)
            for i in range(n):
                if fp[i] == -1:
                    continue
                ii = (i ^ 1) if fp[i ^ 1] != -1 else i
                vp[fp[ii]] = i
        elif fp is None:
            fp = array('i', [-1] * n)
            for i in range(n):
                if vp[i] != -1:
                    ii = (vp[i] ^ 1) if vp[vp[i] ^ 1] != -1 else vp[i]
                    fp[ii] = i

        C._ne = n // 2
        C._vp = vp
        C._fp = fp
        C._half_edges_data = half_edges_data
        C._edges_data = edges_data
        C._mutable = mutable
        C._set_data_pointers()

        if check:
            C._check(ValueError)

        return C

    @classmethod
    def from_string(cls, s, mutable=False, check=True):
        r"""
        Deserialization from string.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph

            sage: T = Triangulation("(~11,4,~3)(~10,~0,11)(~9,0,10)(~8,9,1)(~7,8,~1)(~6,7,2)(~5,6,~2)(~4,5,3)")
            sage: Triangulation.from_string(T.to_string()) == T
            True
        """
        parts = s.split('_')
        ne = uint_from_base64_str(parts[0])
        k_half_edges = uint_from_base64_str(parts[1])
        k_edges = uint_from_base64_str(parts[2])
        mutable = bool(uint_from_base64_str(parts[3]))
        fp = perm_from_base64_str(parts[4], 2 * ne)
        shift = 5
        half_edges_data = tuple(perm_from_base64_str(parts[i], 2 * ne) for i in range(5, 5 + k_half_edges))
        edges_data = tuple(perm_from_base64_str(parts[i], ne) for i in range(5 + k_half_edges, 5 + k_half_edges + k_edges))
        return cls.from_permutations(None, fp, half_edges_data, edges_data, mutable=mutable, check=check)

    def __eq__(self, other):
        r"""
        Return whether ``self`` and ``other`` are equal.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph

            sage: Triangulation("(0,1,2)(~0,~1,~2)") == Triangulation("(0,1,2)(~0,~1,~2)")
            True
            sage: Triangulation("(0,1,2)(~0,~1,~2)") == Triangulation("(0,~0,1)(~1,2,~2)")
            False

            sage: StrebelGraph("(0,1,2,~0,~1,~2)") == StrebelGraph("(0,1,2,~0,~1,~2)")
            True
            sage: StrebelGraph("(0,1,2,~0,~1,~2)") == StrebelGraph("(0,1:1,2,~0,~1,~2)")
            False
        """
        if type(self) != type(other):
            raise TypeError
        return self._ne == other._ne and self._fp == other._fp and self._half_edges_data == other._half_edges_data and self._edges_data == other._edges_data

    def __ne__(self, other):
        r"""
        Return whether ``self`` and ``other`` are different.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph

            sage: Triangulation("(0,1,2)(~0,~1,~2)") != Triangulation("(0,1,2)(~0,~1,~2)")
            False
            sage: Triangulation("(0,1,2)(~0,~1,~2)") != Triangulation("(0,~0,1)(~1,2,~2)")
            True

            sage: StrebelGraph("(0,1,2,~0,~1,~2)") != StrebelGraph("(0,1,2,~0,~1,~2)")
            False
            sage: StrebelGraph("(0,1,2,~0,~1,~2)") != StrebelGraph("(0,1:1,2,~0,~1,~2)")
            True
        """
        if type(self) != type(other):
            raise TypeError
        return self._ne != other._ne or self._fp != other._fp or self._half_edges_data != other._half_edges_data or self._edges_data != other._edges_data

    def _richcmp_(self, other, op):
        r"""
        Compare ``self`` and ``other`` according to the operator ``op``.
        """
        if type(self) != type(other):
            raise TypeError

        c = (self._ne > other._ne) - (self._ne < other._ne)
        if c:
            return rich_to_bool(op, c)

        c = (self._fp > other._fp) - (self._fp < other._fp)
        if c:
            return rich_to_bool(op, c)

        c = (self._half_edges_data > other._half_edges_data) - (self._half_edges_data < other._half_edges_data)
        if c:
            return rich_to_bool(op, c)

        c = (self._edges_data > other._edges_data) - (self._edges_data < other._edges_data)
        return rich_to_bool(op, c)

    def __lt__(self, other):
        return self._richcmp_(other, op_LT)

    def __le__(self, other):
        return self._richcmp_(other, op_LE)

    def __gt__(self, other):
        return self._richcmp_(other, op_GT)

    def __ge__(self, other):
        return self._richcmp_(other, op_GE)

    def copy(self, mutable=None, cls=None):
        r"""
        EXAMPLES::

            sage: from veerer import *

            sage: T = Triangulation([[0,1,2],[-1,-2,-3]], mutable=True)
            sage: U = T.copy()
            sage: T == U
            True
            sage: T.flip(0)
            sage: T == U
            False

            sage: T.set_immutable()
            sage: T.copy() is T
            True

            sage: U = T.copy(mutable=True)
            sage: U.flip(0)
            sage: T
            Triangulation("(0,2,~1)(~0,~2,1)")

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], "RRB", mutable=True)
            sage: S1 = T.copy()
            sage: S2 = T.copy()
            sage: T == S1 == S2
            True
            sage: S1.flip(2, BLUE)
            sage: T == S1
            False
            sage: T == S2
            True

        TESTS::

            sage: from veerer import Triangulation
            sage: T = Triangulation("(0,1,2)(~0,~1,~2)", mutable=True)
            sage: U = T.copy(mutable=False)
            sage: _ = hash(U)

            sage: from veerer import VeeringTriangulation
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", mutable=True)
            sage: U = T.copy(mutable=False)
            sage: _ = hash(U)
        """
        if mutable is None:
            mutable = self._mutable
        if cls is None:
            cls = self.__class__

        if not self._mutable and not mutable:
            # avoid copies of immutable objects
            if type(self) is cls:
                return self
            else:
                T = cls.__new__(cls)
                T._ne = self._ne
                T._fp = self._fp
                T._vp = self._vp
                T._half_edges_data = self._half_edges_data
                T._edges_data = self._edges_data
                T._mutable = mutable
        else:
            T = cls.__new__(cls)
            T._ne = self._ne
            T._fp = self._fp[:]
            T._vp = self._vp[:]
            T._half_edges_data = tuple(l[:] for l in self._half_edges_data)
            T._edges_data = tuple(l[:] for l in self._edges_data)
            T._mutable = mutable

        T._set_data_pointers()
        return T

    def vertex_permutation(self, copy=True):
        if copy:
            return self._vp[:]
        else:
            return self._vp

    def next_at_vertex(self, e, check=True):
        r"""
        EXAMPLES::

            sage: from veerer import Triangulation

            sage: T = Triangulation("(~11,4,~3)(~10,~0,11)(~9,0,10)(~8,9,1)(~7,8,~1)(~6,7,2)(~5,6,~2)(~4,5,3)")
            sage: T.next_at_vertex(0)
            18
            sage: T.next_at_vertex(9)
            7
            sage: T.next_at_vertex(5)
            13
        """
        if check:
            e = self._check_half_edge(e)
        return self._vp[e]

    def previous_at_vertex(self, e, check=True):
        r"""
        EXAMPLES::

            sage: from veerer import Triangulation

            sage: T = Triangulation("(~11,4,~3)(~10,~0,11)(~9,0,10)(~8,9,1)(~7,8,~1)(~6,7,2)(~5,6,~2)(~4,5,3)")
            sage: T.previous_at_vertex(9)
            7
            sage: T.previous_at_vertex(8)
            10
            sage: T.previous_at_vertex(4)
            11
        """
        if check:
            e = self._check_half_edge(e)
        return self._fp[self._ep(e)]

    def edge_permutation(self, copy=True):
        r"""
        EXAMPLES::

            sage: from veerer import Triangulation

            sage: Triangulation("(0,1,2)(~0,~1,~2)").edge_permutation()
            array('i', [1, 0, 3, 2, 5, 4])
            sage: Triangulation("(0,1,2)").edge_permutation()
            array('i', [0, -1, 2, -1, 4, -1])
        """
        return array('i', [self._ep(e) for e in range(2 * self._ne)])

    def next_in_edge(self, e, check=True):
        if check:
            self._check_half_edge(e)
        return self._ep(e)

    def previous_in_edge(self, e, check=True):
        if check:
            self._check_half_edge(e)
        return self._vp[self._fp[e]]

    def face_permutation(self, copy=True):
        if copy:
            return self._fp[:]
        else:
            return self._fp

    def next_in_face(self, e, check=True):
        if check:
            e = self._check_half_edge(e)
        return self._fp[e]

    def previous_in_face(self, e, check=True):
        r"""
        EXAMPLES::

            sage: from veerer import Triangulation

            sage: T = Triangulation("(~11,4,~3)(~10,~0,11)(~9,0,10)(~8,9,1)(~7,8,~1)(~6,7,2)(~5,6,~2)(~4,5,3)")
            sage: T.previous_in_face(10)
            9
            sage: T.previous_in_face(1)
            21
            sage: T.previous_in_face(3)
            16
        """
        if check:
            e = self._check_half_edge(e)
        return self._ep(self._vp[e])

    def half_edges(self):
        for e in range(self._ne):
            yield 2 * e
            if self._vp[2 * e + 1] != -1:
                yield 2 * e + 1

    def num_half_edges(self):
        r"""
        Return the number of half edges.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: Triangulation("(0,1,2)(~1,3,4)").num_half_edges()
            6
        """
        return sum(self._vp[i] != -1 for i in range(2 * self._ne))

    def has_folded_edge(self):
        r"""
        EXAMPLES::

            sage: from veerer import Triangulation
            sage: Triangulation("(0,1,2)(~0,~1,~2)").has_folded_edge()
            False
            sage: Triangulation("(0,1,2)").has_folded_edge()
            True
        """
        return any(self._vp[2 * i + 1] == -1 for i in range(self._ne))

    def folded_edges(self):
        r"""
        Iterate through half-edges on a folded edge.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: list(Triangulation("(0,1,2)(~0,~1,~2)").folded_edges())
            []
            sage: list(Triangulation("(0,1,2)").folded_edges())
            [0, 2, 4]
        """
        vp = self._vp
        for i in range(self._ne):
            if vp[2 * i + 1] == -1:
                yield 2 * i

    def num_folded_edges(self):
        r"""
        Return the number of folded edges.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: Triangulation("(0,1,2)(~0,~1,~2)").num_folded_edges()
            0
            sage: Triangulation("(0,1,2)").num_folded_edges()
            3
        """
        return sum(self._vp[i] == -1 for i in range(1, 2 * self._ne, 2))

    def num_edges(self):
        r"""
        Return the number of edges.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: Triangulation("(0,1,2)(~0,~1,~2)").num_edges()
            3
            sage: Triangulation("(0,1,2)").num_edges()
            3
        """
        return self._ne

    def _edge_rep(self, e):
        import warnings
        warnings.warn("Constellation._edge_rep is deprecated")
        return self._half_edge_string(e)

    def _norm(self, e):
        import warnings
        warnings.warn("Constellation._norm is deprecated")
        return e ^ 1 if e % 2 else e

    def _half_edge_string(self, e):
        return '~%d' % (e // 2) if e % 2 else '%d' % (e // 2)

    def edges(self):
        r"""
        Return the list of edges as tuples of half-edges

        EXAMPLES::

            sage: from veerer import *

            sage: T = Triangulation("(0,1,2)(3,4,5)(~0,~3,6)")
            sage: T.edges()
            [[0, 1], [2], [4], [6, 7], [8], [10], [12]]
        """
        vp = self._vp
        return [[2 * i] if vp[2 * i + 1] == -1 else [2 * i, 2 * i + 1] for i in range(self._ne)]

    def vertices(self):
        r"""
        Return the list of vertices as tuples of half-edges

        EXAMPLES::

            sage: from veerer import *

            sage: T = Triangulation("(0,1,2)(3,4,5)(~0,~3,6)")
            sage: T.vertices()
            [[0, 4, 2, 1, 12, 6, 10, 8, 7]]
        """
        return perm_cycles(self._vp, True, 2 * self._ne)

    def num_vertices(self):
        r"""
        Return the number of vertices.

        EXAMPLES::

            sage: from veerer import Triangulation

            sage: T = Triangulation("(0,1,2)(3,4,5)(~0,~3,6)")
            sage: T.num_vertices()
            1
        """
        return perm_num_cycles(self._vp, 2 * self._ne)

    def faces(self):
        r"""
        Return the list of edges as tuples of half-edges

        EXAMPLES::

            sage: from veerer import Triangulation

            sage: T = Triangulation("(0,1,2)(3,4,5)(~0,~3,6)")
            sage: T.faces()
            [[0, 2, 4], [1, 7, 12], [6, 8, 10]]
        """
        return perm_cycles(self._fp, True, 2 * self._ne)

    def num_faces(self):
        r"""
        Return the number of faces.

        EXAMPLES::

            sage: from veerer import Triangulation

            sage: T = Triangulation("(0,1,2)(3,4,5)(~0,~3,6)")
            sage: T.num_faces()
            3
        """
        return perm_num_cycles(self._fp, 2 * self._ne)

    def is_connected(self):
        r"""
        Return whether the constellation is connected.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: Triangulation("(0,1,2)(3,4,5)(~0,~3,6)").is_connected()
            True
            sage: Triangulation("(0,1,2)(3,4,5)").is_connected()
            False
        """
        return perms_are_transitive((self._vp, self._fp), 2 * self._ne)

    def connected_components(self):
        r"""
        Return the connected components as a list of lists of half-edges.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: T = Triangulation("(0,1,3)(~0,~1,~3)(2,4,5)(~2,~4,~5)")
            sage: T.connected_components()
            [[0, 1, 2, 3, 6, 7], [4, 5, 8, 9, 10, 11]]

        To construct the triangulation induced on each connected component, one can
        use the method :meth:`subgraph`::

            sage: c0, c1 = T.connected_components()
            sage: T.subgraph(c0)
            Triangulation("(0,1,2)(~0,~1,~2)")
            sage: T.subgraph(c1)
            Triangulation("(0,1,2)(~0,~1,~2)")
        """
        return perms_orbits((self._vp, self._fp), 2 * self._ne)

    def subgraph(self, half_edges, mapping=False, mutable=False, check=True):
        r"""
        Return the subgraph of this constellation induced on ``half_edges``.

        Note that ``half_edges`` must be invariant under the edge permutation.
        """
        if check:
            half_edges = [self._check_half_edge(e) for e in half_edges]
            S = set(half_edges)
            if len(S) != len(half_edges):
                raise ValueError('redundant half_edges')
            if any(self._ep(e) not in S for e in S):
                raise ValueError('half_edges not stable under the edge permutation')

        n = len(half_edges)
        relabel = [None] * (2 * self._ne)
        for i, j in enumerate(half_edges):
            relabel[j] = i
        vp = array('i', [-1] * n)
        ep = array('i', [-1] * n)

        for e_induced, e_orig in enumerate(half_edges):
            ep[e_induced] = relabel[self._ep(e_orig)]

            e = self._vp[e_orig]
            while relabel[e] is None:
                e = self._vp[e]
            vp[e_induced] = relabel[e]

        half_edges_data = []
        for l in self._half_edges_data:
            half_edges_data.append(array('i', [l[e] for e in half_edges]))

        edges = [e // 2 for e in half_edges if e % 2 == 0]
        edges_data = []
        for l in self._edges_data:
            edges_data.append(array('i', [l[e] for e in edges]))

        output = self.__class__.from_permutations(vp, None, half_edges_data, edges_data, mutable=mutable, check=True)
        return (output, relabel) if mapping else output

    def connected_components_subgraphs(self, mutable=False):
        r"""
        Run through the connected components as graphs.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: T = Triangulation("(0,1,3)(~0,~1,~3)(2,4,5)(~2,~4,~5)")
            sage: list(T.connected_components_subgraphs())
             [Triangulation("(0,1,2)(~0,~1,~2)"), Triangulation("(0,1,2)(~0,~1,~2)")]
        """
        for comp in self.connected_components():
            yield self.subgraph(comp)

    def swap(self, e, check=True):
        r"""
        Change the orientation of the edge ``e``.

        EXAMPLES::

            sage: from veerer import Triangulation

            sage: T = Triangulation("(0,1,2)(~0,~1,~2)", mutable=True)
            sage: T.swap(0)
            sage: T
            Triangulation("(0,~1,~2)(~0,1,2)")
            sage: T.swap(1)
            sage: T
            Triangulation("(0,1,2)(~0,~1,~2)")
            sage: T.swap(2)
            sage: T
            Triangulation("(0,~1,2)(~0,1,~2)")

            sage: T = Triangulation("(0,~5,4)(3,5,6)(1,2,~6)", mutable=True)
            sage: T.swap(0)
            sage: T
            Triangulation("(0,~5,4)(1,2,~6)(3,5,6)")
            sage: T.swap(10)
            sage: T
            Triangulation("(0,5,4)(1,2,~6)(3,~5,6)")

        Also works for veering triangulations::

            sage: from veerer import VeeringTriangulation

            sage: fp = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: cols = "BRBBBRRBBBBR"
            sage: V = VeeringTriangulation(fp, cols, mutable=True)
            sage: V.swap(0)
            sage: V.swap(20)
            sage: V
            VeeringTriangulation("(0,1,~3)(~0,~1,2)(~2,~4,6)(3,4,~5)(5,~9,~7)(~6,8,7)(~8,10,11)(9,~10,~11)", "BRBBBRRBBBBR")

        One can alternatively use ``relabel``::

            sage: T = Triangulation("(0,~5,4)(1,2,~6)(3,5,6)", mutable=True)
            sage: T1 = T.copy()
            sage: T1.swap(10)
            sage: T1.swap(12)
            sage: T2 = T.copy()
            sage: T2.relabel("(5,~5)(6,~6)")
            sage: T1 == T2
            True
        """
        if not self._mutable:
            raise ValueError('immutable triangulation; use a mutable copy instead')

        if check:
            e = self._check_half_edge(e)

        vp = self._vp
        ep = self._ep
        fp = self._fp
        E = ep(e)

        if e == E:
            return

        # images/preimages by vp
        e_vp = vp[e]
        E_vp = vp[E]
        e_vp_inv = fp[E]
        E_vp_inv = fp[e]
        assert vp[e_vp_inv] == e
        assert vp[E_vp_inv] == E

        # images/preimages by fp
        e_fp = fp[e]
        E_fp = fp[E]
        e_fp_inv = ep(e_vp)
        E_fp_inv = ep(E_vp)
        assert fp[e_fp_inv] == e
        assert fp[E_fp_inv] == E

        fp[e_fp_inv] = E
        fp[E_fp_inv] = e
        vp[e_vp_inv] = E
        vp[E_vp_inv] = e
        fp[e] = E_fp
        fp[E] = e_fp
        vp[e] = E_vp
        vp[E] = e_vp

        for l in self._half_edges_data:
            l[e], l[E] = l[E], l[e]

    def relabel(self, p, check=True):
        r"""
        Relabel this triangulation inplace according to the permutation ``p``.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph, BLUE, RED

            sage: T = Triangulation("(0,1,2)(~0,~1,~2)", mutable=True)
            sage: T.relabel("(0,~0)")
            sage: T
            Triangulation("(0,~1,~2)(~0,1,2)")
            sage: T.relabel("(0,1,~2)(~0,~1,2)")
            sage: T
            Triangulation("(0,1,2)(~0,~1,~2)")

            sage: T.set_immutable()
            sage: T.relabel("(0,~1)")
            Traceback (most recent call last):
            ...
            ValueError: immutable triangulation; use a mutable copy instead

        An example of a flip sequence which forms a loop after non-trivial relabelling::

            sage: T0 = Triangulation("(1,~0,4)(2,~4,~1)(3,~2,5)(~5,~3,0)")
            sage: T = T0.copy(mutable=True)
            sage: T.flip_back(2) # 1
            sage: T.flip_back(6) # 3
            sage: T.flip_back(0) # 0
            sage: T.flip_back(4) # 2
            sage: T.relabel("(0,2)(1,3)(~0,~2)(~1,~3)")
            sage: T == T0
            True

        An example with boundary::

            sage: t = Triangulation("(0,1,2)(~0,3,4)(~4,~3,~2,~1)", {"~1": 1, "~2": 1, "~3": 1, "~4": 1}, mutable=True)
            sage: t.relabel("(0,3)(1,~2)(~0,~3)(~1,2)")
            sage: t
            Triangulation("(0,4,~3)(~1,3,~2)(~0:1,1:1,2:1,~4:1)")

        Veering triangulations::

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBB", mutable=True)
            sage: T.relabel([0,1,3,2,5,4])
            sage: T
            VeeringTriangulation("(0,~1,~2)(~0,1,2)", "RBB")
            sage: T._check()

        Composing relabellings and permutation composition::

            sage: from veerer.permutation import perm_compose, perm_random_centralizer
            sage: fp = "(0,16,~15)(1,19,~18)(2,22,~21)(3,21,~20)(4,20,~19)(5,23,~22)(6,18,~17)(7,17,~16)(8,~1,~23)(9,~2,~8)(10,~3,~9)(11,~4,~10)(12,~5,~11)(13,~6,~12)(14,~7,~13)(15,~0,~14)"
            sage: cols = "RRRRRRRRBBBBBBBBBBBBBBBB"
            sage: T0 = VeeringTriangulation(fp, cols)
            sage: ep = T0.edge_permutation()
            sage: for _ in range(10):
            ....:     p1 = perm_random_centralizer(ep)
            ....:     p2 = perm_random_centralizer(ep)
            ....:     T1 = T0.copy(mutable=True)
            ....:     T1.relabel(p1)
            ....:     T1.relabel(p2)
            ....:     T2 = T0.copy(mutable=True)
            ....:     T2.relabel(perm_compose(p1, p2))
            ....:     assert T1  == T2

        TESTS:

        This example used to be wrong::

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE], mutable=True)
            sage: from veerer.permutation import perm_random_centralizer
            sage: for _ in range(10):
            ....:     r = perm_random_centralizer(T.edge_permutation())
            ....:     T.relabel(r)
            ....:     T._check()
        """
        if not self._mutable:
            raise ValueError('immutable triangulation; use a mutable copy instead')

        n = 2 * self._ne
        if check and not perm_check(p, n):
            # if the input is not a valid permutation, we assume that half-edges
            # are not separated
            if isinstance(p, str):
                p = perm_init(p, 2 * self._ne, edge_like=True)
            else:
                p = perm_init(p, 2 * self._ne)

            for i in range(0, n, 2):
                if p[i] == -1 or (p[i + 1] != -1 and p[i] // 2 != p[i + 1] // 2):
                    raise ValueError("invalid relabelling permutation p={}".format(perm_cycle_string(p, edge_like=True)))

        # TODO: would better be inplace!!
        self._vp = perm_conjugate(self._vp, p)
        self._fp = perm_conjugate(self._fp, p)
        for l in self._half_edges_data:
            perm_on_list(p, l, n)

        for l in self._edges_data:
            perm_on_edge_list(p, l, n)

        self._check()

    def _relabelling_from(self, root):
        r"""
        When connected, return a canonical relabelling map obtained from walking
        along the triangulation starting at ``root``.

        The returned relabelling array maps the current edge to the new
        labelling.

        EXAMPLES::

            sage: from veerer import *
            sage: from array import array

        The torus example (6 symmetries)::

            sage: fp = array('i', [2, 3, 5, 4, 1, 0])
            sage: vp = array('i', [4, 5, 1, 0, 2, 3])
            sage: T = Triangulation.from_permutations(vp, fp, (array('i', [0]*6),), mutable=True)
            sage: T._relabelling_from(3)
            array('i', [5, 4, 1, 0, 2, 3])

            sage: p = T._relabelling_from(0)
            sage: T.relabel(p)
            sage: for i in range(6):
            ....:     p = T._relabelling_from(i)
            ....:     S = T.copy()
            ....:     S.relabel(p)
            ....:     assert S == T

        The sphere example (3 symmetries)::

            sage: fp = array('i', [2, -1, 4, -1, 0, -1])
            sage: vp = array('i', [4, -1, 0, -1, 2, -1])
            sage: T = Triangulation.from_permutations(vp, fp, (array('i', [0]*6),), mutable=True)
            sage: T._relabelling_from(2)
            array('i', [4, 5, 0, 1, 2, 3])
            sage: p = T._relabelling_from(0)
            sage: T.relabel(p)
            sage: for i in range(3):
            ....:     p = T._relabelling_from(2 * i)
            ....:     S = T.copy()
            ....:     S.relabel(p)
            ....:     assert S == T

        An example with no automorphism::

            sage: T = Triangulation("(0,1,2)(3,4,5)(~0,~3,6)", mutable=True)
            sage: p = T._relabelling_from(0)
            sage: T.relabel(p)
            sage: for i in T.half_edges():
            ....:     if i == 0: continue
            ....:     p = T._relabelling_from(i)
            ....:     S = T.copy()
            ....:     S.relabel(p)
            ....:     S._check()
            ....:     assert S != T
        """
        root = self._check_half_edge(root)
        relabelling = array('i', [-1] * (2 * self._ne))
        last = edge_relabelling_from(relabelling, self._fp, self._ne * 2, root, 0)
        if last // 2 != self._ne:
            raise ValueError("non-connected constellation")
        return relabelling

    def automorphisms(self):
        r"""
        Return the list of automorphisms of this triangulation.

        The output is a list of arrays that are permutations acting on the set
        of half edges.

        For triangulations with boundaries, we allow automorphism to permute
        boundaries. Though, boundary edge have to be mapped on boundary edge.

        EXAMPLES::

            sage: from veerer import *

        An example with 4 symmetries in genus 2::

            sage: T = Triangulation("(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)")
            sage: A = T.automorphisms()
            sage: len(A)
            4

        And the "sphere octagon" has 8::

            sage: s  = "(0,8,~7)(1,9,~0)(2,10,~1)(3,11,~2)(4,12,~3)(5,13,~4)(6,14,~5)(7,15,~6)"
            sage: len(Triangulation(s).automorphisms())
            8

        A veering triangulation with 4 symmetries in genus 2::

            sage: fp = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: cols = "BRBBBRRBBBBR"
            sage: V = VeeringTriangulation(fp, cols)
            sage: A = V.automorphisms()
            sage: len(A)
            4
            sage: S = V.copy(mutable=True)
            sage: for a in A:
            ....:     S.relabel(a)
            ....:     assert S == V

        Examples with boundaries::

            sage: t = Triangulation("(0,1,2)", boundary="(~0:1)(~1:1)(~2:1)")
            sage: len(t.automorphisms())
            3
            sage: t = Triangulation("(0,1,2)", boundary="(~0:1,~1:1,~2:1)")
            sage: len(t.automorphisms())
            3
            sage: t = Triangulation("(0,1,2)", boundary="(~0:1,~1:1,~2:2)")
            sage: len(t.automorphisms())
            1

        Linear families::

            sage: s = StrebelGraph("(0,3,7,~6,~2,1)(2,5,~4,~3,~1,~0)(4,8,~5)(6,~8,~7)")
            sage: f = StrebelGraphLinearFamily(s, [(2, 0, 0, 0, 1, 0, 1, 0, 2), (0, 2, 0, 0, 0, 1, 0, 1, 2), (0, 0, 1, 1, 0, 0, 0, 0, 2)])
            sage: len(f.automorphisms())
            2
        """
        if self.is_connected():
            best_relabellings = self.best_relabelling(all=True)[0]
            p0 = perm_invert(best_relabellings[0])
            return [perm_compose(p, p0) for p in best_relabellings]
        else:
            raise NotImplementedError

    def best_relabelling(self, all=False):
        r"""
        Return a pair ``(r, data)`` where ``r`` is a relabelling that
        brings this constellation to the canonical one.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph
            sage: from veerer.permutation import perm_random_centralizer

            sage: examples = []
            sage: triangles = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: examples.append(Triangulation(triangles, mutable=True))
            sage: fp = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: cols = "BRBBBRRBBBBR"
            sage: examples.append(VeeringTriangulation(fp, cols, mutable=True))
            sage: examples.append(StrebelGraph("(0,6,~5,~3,~1,4,~4:3,2,~2:3)(1:2)(3:2,~0)(5:2)(~6)", mutable=True))

            sage: for G in examples:
            ....:     print(G)
            ....:     r, (fp, half_edges_data, edges_data) = G.best_relabelling()
            ....:     for _ in range(10):
            ....:         p = perm_random_centralizer(G.edge_permutation())
            ....:         G.relabel(p)
            ....:         r2, (fp2, half_edges_data2, edges_data2) = G.best_relabelling()
            ....:         assert fp2 == fp, G
            ....:         assert half_edges_data2 == half_edges_data, G
            ....:         assert edges_data2 == edges_data, G
            Triangulation("(0,~1,2)(~0,1,~3)(~2,~4,6)(3,4,~5)(5,~9,~7)(~6,8,7)(~8,~10,11)(9,10,~11)")
            VeeringTriangulation("(0,~1,2)(~0,1,~3)(~2,~4,6)(3,4,~5)(5,~9,~7)(~6,8,7)(~8,~10,11)(9,10,~11)", "BRBBBRRBBBBR")
            StrebelGraph("(0,6,~5,~3,~1,4,~4:3,2,~2:3)(~0,3:2)(1:2)(5:2)(~6)")
        """
        if not self.is_connected():
            # each compoent is labelled with consecutive half-edge labels
            # we use canonical labels for each of them, and then use a total ordering on the components
            component_number = [-1] * self._n
            relabel = [-1] * self._n
            components = []
            for cc_num, cc in enumerate(self.connected_components()):
                # relabel_local is a partial map: {edges in self} -> {edges in image}
                vt, relabel_local = self.subgraph(cc, mapping=True, mutable=True)
                r, _ = vt.best_relabelling()
                vt.relabel(r)
                for i, j in enumerate(relabel_local):
                    if j is None:
                        continue
                    component_number[i] = cc_num
                    relabel[i] = r[j]
                components.append((vt, cc_num))

            components.sort()
            # now glue permutations and relabelling
            # TODO: the edge permutation will not be in canonical form!!!!!
            shift = 0
            vp = array('i', [-1] * self._n)
            fp = array('i', [-1] * self._n)
            for (vt, cc_num) in components:
                for e in range(vt._n):
                    vp[shift + e] = shift + vt._vp[e]
                    fp[shift + e] = shift + vt._fp[e]

        n = 2 * self._ne
        fp = self._fp

        best = None
        if all:
            relabellings = []

        for start_edge in self.half_edges():
            if fp[start_edge] == -1:
                continue
            relabelling = self._relabelling_from(start_edge)

            fp_new = perm_conjugate(fp, relabelling)
            half_edges_data_new = [l[:] for l in self._half_edges_data]
            for l in half_edges_data_new:
                perm_on_list(relabelling, l, 2 * self._ne)
            edges_data_new = [l[:] for l in self._edges_data]
            for l in edges_data_new:
                perm_on_edge_list(relabelling, l, 2 * self._ne)

            T = (fp_new, half_edges_data_new, edges_data_new)
            if best is None or T < best:
                best_relabelling = relabelling
                best = T
                if all:
                    del relabellings[:]
                    relabellings.append(relabelling)
            elif all and T == best:
                relabellings.append(relabelling)

        return (relabellings, best) if all else (best_relabelling, best)

    def set_canonical_labels(self):
        r"""
        Set labels in a canonical way in its automorphism class.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.permutation import perm_random, perm_random_centralizer

            sage: t = [(-12, 4, -4), (-11, -1, 11), (-10, 0, 10), (-9, 9, 1),
            ....:      (-8, 8, -2), (-7, 7, 2), (-6, 6, -3), (-5, 5, 3)]
            sage: T = Triangulation(t, mutable=True)
            sage: T
            Triangulation("(0,10,~9)(~0,11,~10)(1,~8,9)(~1,~7,8)(2,~6,7)(~2,~5,6)(3,~4,5)(~3,~11,4)")
            sage: T.set_canonical_labels()
            sage: T
            Triangulation("(0,1,2)(~0,~2,3)(~1,4,5)(~3,6,7)(~4,8,~5)(~6,9,~7)(~8,10,11)(~9,~11,~10)")
        """
        if not self._mutable:
            raise ValueError('immutable triangulation; use a mutable copy instead')

        r, _ = self.best_relabelling()
        self.relabel(r, check=False)

    def iso_sig(self):
        r"""
        Return a canonical signature.

        EXAMPLES::

            sage: from veerer import *
            sage: T = Triangulation("(0,3,1)(~0,4,2)(~1,~2,~4)")
            sage: T.iso_sig()
            '5_1__1_2~46098537_0000000000'
            sage: TT = Triangulation.from_string(T.iso_sig())
            sage: TT
            Triangulation("(0,1,2)(~1,3,4)(~2,~4,~3)")
            sage: TT.iso_sig() == T.iso_sig()
            True

            sage: T = Triangulation("(0,10,~6)(1,12,~2)(2,14,~3)(3,16,~4)(4,~13,~5)(5,~1,~0)(6,~17,~7)(7,~14,~8)(8,13,~9)(9,~11,~10)(11,~15,~12)(15,17,~16)")
            sage: T.iso_sig()
            'i_1__1_264a0e8i1mcj3sgr5tkq7xov9dbupwfzhyln_000000000000000000000000000000000000'
            sage: Triangulation.from_string(T.iso_sig())
            Triangulation("(0,1,2)(~0,3,4)(~1,5,6)(~2,7,8)(~3,9,10)(~4,11,12)(~5,~9,13)(~6,14,~12)(~7,~13,15)(~8,~14,16)(~10,~16,17)(~11,~15,~17)")

            sage: t = [(-12, 4, -4), (-11, -1, 11), (-10, 0, 10), (-9, 9, 1),
            ....:      (-8, 8, -2), (-7, 7, 2), (-6, 6, -3), (-5, 5, 3)]
            sage: cols = [RED, RED, RED, RED, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE]
            sage: T = VeeringTriangulation(t, cols, mutable=True)
            sage: T.iso_sig()
            'c_1_1_1_2548061cag39ei7dbkfnmjhl_000000000000000000000000_122212122212'

        If we relabel the triangulation, the isomorphic signature does not change::

            sage: from veerer.permutation import perm_random_centralizer
            sage: p = perm_random_centralizer(T.edge_permutation())
            sage: T.relabel(p)
            sage: T.iso_sig()
            'c_1_1_1_2548061cag39ei7dbkfnmjhl_000000000000000000000000_122212122212'

        An isomorphic triangulation can be reconstructed from the isomorphic
        signature via::

            sage: s = T.iso_sig()
            sage: T2 = VeeringTriangulation.from_string(s)
            sage: T == T2
            False
            sage: T.is_isomorphic_to(T2)
            True

        TESTS::

            sage: from veerer.veering_triangulation import VeeringTriangulation
            sage: from veerer.permutation import perm_random

            sage: t = [(-12, 4, -4), (-11, -1, 11), (-10, 0, 10), (-9, 9, 1),
            ....:      (-8, 8, -2), (-7, 7, 2), (-6, 6, -3), (-5, 5, 3)]
            sage: cols = [RED, RED, RED, RED, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE]
            sage: T = VeeringTriangulation(t, cols, mutable=True)
            sage: iso_sig = T.iso_sig()
            sage: for _ in range(10):
            ....:     p = perm_random_centralizer(T.edge_permutation())
            ....:     T.relabel(p)
            ....:     assert T.iso_sig() == iso_sig

            sage: VeeringTriangulation("(0,1,2)(3,4,~1)(5,6,~4)", "RBGGRBG").iso_sig()
            '7_1_1_1_2~4~068~5ac~9~_00000000000000_8128128'
            sage: VeeringTriangulation.from_string('7_1_1_1_2~4~068~5ac~9~_00000000000000_8128128')
            VeeringTriangulation("(0,1,2)(~2,3,4)(~4,5,6)", "GRBGRBG")
        """
        T = self.copy(mutable=True)
        T.set_canonical_labels()
        return T.to_string()

    def _non_isom_easy(self, other):
        r"""
        A quick certificate of non-isomorphism that does not require relabellings.
        """
        return (self._ne != other._ne or
            perm_cycle_type(self._vp) != perm_cycle_type(other._vp) or
            self.num_folded_edges() != other.num_folded_edges() or
            perm_cycle_type(self._fp) != perm_cycle_type(other._fp) or
            any(sorted(l_self) != sorted(l_other) for l_self, l_other in zip(self._half_edges_data, other._half_edges_data)) or
            any(sorted(l_self) != sorted(l_other) for l_self, l_other in zip(self._edges_data, other._edges_data)))

    def is_isomorphic(self, other, certificate=False):
        r"""
        Check whether ``self`` is isomorphic to ``other``.

        TESTS::

            sage: from veerer import Triangulation, VeeringTriangulation
            sage: from veerer.permutation import perm_random_centralizer

            sage: T = Triangulation("(0,5,1)(~0,4,2)(~1,~2,~4)(3,6,~5)", mutable=True)
            sage: TT = T.copy()
            sage: for _ in range(10):
            ....:     rel = perm_random_centralizer(TT.edge_permutation())
            ....:     TT.relabel(rel)
            ....:     assert T.is_isomorphic(TT)

            sage: fp = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: cols = "BRBBBRRBBBBR"
            sage: V = VeeringTriangulation(fp, cols, mutable=True)
            sage: W = V.copy()
            sage: p = perm_random_centralizer(V.edge_permutation())
            sage: W.relabel(p)
            sage: assert V.is_isomorphic(W) is True
            sage: ans, cert = V.is_isomorphic(W, True)
            sage: V.relabel(cert)
            sage: assert V == W
        """
        if type(self) is not type(other):
            raise TypeError("can only check isomorphisms between identical types")

        if self._non_isom_easy(other):
            return (False, None) if certificate else False

        r1, data1 = self.best_relabelling()
        r2, data2 = other.best_relabelling()

        if data1 != data2:
            return (False, None) if certificate else False
        elif certificate:
            return (True, perm_compose(r1, perm_invert(r2)))
        else:
            return True
