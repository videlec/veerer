r"""
Constellations

A *constellation* is a graph cellularly embedded on an orientable
surface. The main class in this file is
:class:`~veerer.constellation.Constellation` which is the common base claas for
:class:`~veerer.triangulation.Triangulation`,
:class:`~veerer.veering_triangulation.VeeringTriangulation` and
:class:`~veerer.strebel_graph.StrebelGraph`.
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2018 Mark Bell
#                     2018-2026 Vincent Delecroix
#                     2024-2026 Kai Fu
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
import itertools
import numbers
from array import array

from sage.structure.richcmp import op_LT, op_LE, op_EQ, op_NE, op_GT, op_GE, rich_to_bool

from .permutation import (perm_init, perm_check, perm_cycles, perm_on_array, perm_on_edge_array,
                          perm_invert, perm_conjugate, perm_cycle_string, perm_cycles_lengths,
                          perm_cycles_to_string, perm_on_list, perm_on_edge_list, perm_cycle_type,
                          perm_num_cycles, str_to_cycles, str_to_cycles_and_data, perm_compose, perm_from_base64_str,
                          uint_base64_str, uint_from_base64_str, perm_base64_str,
                          perms_are_transitive, perms_orbits, perm_edge_orbits, edge_relabelling_from)


def check_relabelling(arg, ne):
    r"""
    EXAMPLES::

        sage: from veerer.constellation import check_relabelling
        sage: from veerer.permutation import perm_cycle_string
        sage: p = check_relabelling("(0,1,2)", 3)
        sage: perm_cycle_string(p, edge_like=True)
        '(0,1,2)(~0,~1,~2)'
        sage: p = check_relabelling("(0,1,2)(~0,~1,~2)", 3)
        sage: perm_cycle_string(p, edge_like=True)
        '(0,1,2)(~0,~1,~2)'
        sage: p = check_relabelling("(0,~1,2)", 3)
        sage: perm_cycle_string(p, edge_like=True)
        '(0,~1,2)(~0,1,~2)'
        sage: p = check_relabelling("(0,1,2,~0,~1,~2)", 3)
        sage: perm_cycle_string(p, edge_like=True)
        '(0,1,2,~0,~1,~2)'
    """
    n = 2 * ne
    if isinstance(arg, str):
        p = perm_init(arg, n, edge_like=True, partial=True)
    else:
        p = perm_init(arg, n, partial=True)

    if len(p) != n:
        raise ValueError("len(p) = {} while n = {}".format(len(p), n))

    for h in range(n):
        if p[h] == -1 and p[h ^ 1] == -1:
            p[h] = h
            p[h ^ 1] = h ^ 1
        elif p[h] == -1:
            p[h] = p[h ^ 1] ^ 1
        elif p[h ^ 1] == -1:
            p[h ^ 1] = p[h] ^ 1
        elif p[h ^ 1] != p[h] ^ 1:
            raise ValueError("invalid input for relabelling (arg={})".format(arg))

    if not perm_check(p, n):
        raise ValueError("invalid input for relabelling (arg={})".format(arg))

    return p



class Constellation:
    r"""
    Graph cellularly embedded in an oriented surface.

    Such graph is encoded with the half-edge data structure: a vertex
    permutation ``vp`` and a face permutation ``fp`` (the edge permutation is
    implicit). Each cycle of ``vp`` and ``fp`` corresponds to a vertex and
    a face respectively. More precisely, this class has three main attributes

    * _ne  number of edges (an int)
    * _fp  face permutation (an array)
    * _vp  vertex permutation (an array)

    Our conventions for the permutations are set out in the following figure::

              ~b
            ----->
        w-----------*-----------v
         \             <-----  /
          \ \             b   / /
           \ \ c             / /~a
            \ \     F       / /
             \ v           / v
              *         ^ *
             ^ \       / /
              \ \   a / /
             ~c\ \   / /
                \ \   /
                   \ /
                    u

    Here the face permutation sends a to b, b to c, and c to a. The
    vertex permutation send a to ~c, b to ~a, and c to ~b. The (implicit) edge
    permutation interchanges e and ~e for every edge; the edge e is folded if
    and only if e = ~e.  Thus folded edges are fixed by the edge permutation.

    The half-edges are encoded by integers and an edge in the edge permutation
    is always a cycle `(2e, 2e+1)` for some non-negative integer `e`. A folded
    edge is a cycle `(2e)` (in which case the integer `2e+1` is not coding
    any half-edge).

    The class implements a mutability flag by mean of a boolean attribute

    * _mutable

    When immutable the class has an associated hash value and could be used in
    a set or as keys of dictionaries. The functions that modify the data
    structure will raise an error when immutable.

    Finally, the edges and half-edges could carry data that will be used in
    the computation of the hash value and the canonical labelling. These
    extra data are stored in

    * _half_edges_data
    * _edges_data
    """
    __slots__ = ['_constellation_class',  # subclass of Constellation
                 '_mutable',  # mutability flag
                 '_ne',  # number of edges
                 '_vp',  # vertex permutation
                 '_fp',  # face permutation
                 '_half_edges_data',  # a list of half-edges data: each element is an array of length 2 * _ne
                 '_edges_data',  # a list of edges data: each element is an array of length _ne
                ]

    def __init__(self, ne, vp, fp, half_edges_data, edges_data, mutable=False, check=True):
        try:
            cls = self._constellation_class
        except AttributeError:
            self._constellation_class = Constellation
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

        if fp is None:
            fp = self._fp = array('i', [-1] * (2 * ne))
            for i in range(2 * ne):
                if vp[i] == -1:
                    continue
                ii = vp[i] ^ 1 if vp[i] != -1 else vp[i]
                fp[ii] = i
        else:
            self._fp = fp

        self._half_edges_data = half_edges_data
        self._edges_data = edges_data
        self._mutable = mutable
        self._set_data_pointers()

        if check:
            self._check(ValueError)

    def _assert_mutable(self):
        r"""
        Helper that raises a ``ValueError`` if this object is not mutable.

        TESTS::

            sage: from veerer import VeeringTriangulation
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: T._assert_mutable()
            Traceback (most recent call last):
            ...
            ValueError: immutable VeeringTriangulation; use a mutable copy instead
            sage: T.copy(mutable=True)._assert_mutable()
        """
        if not self._mutable:
            raise ValueError(f"immutable {type(self).__name__}; use a mutable copy instead")

    def _ep(self, h):
        r"""
        Return the image of ``h`` under the edge permutation.
        """
        if self._vp[h] == -1:
            return -1
        elif self._vp[h ^ 1] == -1:
            return h
        else:
            return h ^ 1

    def _set_data_pointers(self):
        pass

    def _check(self, error=RuntimeError):
        r"""
        Helper function to check the data structure.

        By default a ``RuntimeError`` is raised but it could be changed by
        providing an optional ``error`` argument.
        """
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

        for i in range(2 * ne):
            if self._vp[i] != -1 and self._fp[self._ep(self._vp[i])] != i:
                raise error('fev relation not satisfied at half-edge i={}'.format(self._half_edge_string(i)))

        if not isinstance(self._half_edges_data, tuple):
            raise ValueError("half_edges_data must be a tuple")
        for l in self._half_edges_data:
            if not isinstance(l, array) or l.typecode != 'i' or len(l) != 2 * ne:
                raise ValueError("each half edge data must be an array of length twice the number of edges: got {}".format(type(l)))
            for i in range(2 * ne):
                if self._vp[i] == -1:
                    if l[i]:
                        raise error('non-zero entry {} in half-edge data at the non-active half-edge {}'.format(l[i], i))

        if not isinstance(self._edges_data, tuple):
            raise ValueError("edges_data must be a tuple")
        for l in self._edges_data:
            if not isinstance(l, array) or l.typecode != 'i' or len(l) != ne:
                raise error("each edges data must be an array of length the number of edges; got a {} of length {}".format(type(l).__name__, len(l)))

    def _realloc(self, n_max):
        if self._half_edges_data or self._edges_data:
            raise NotImplementedError
        if n_max < self._n:
            return
        self._vp.extend([-1] * (n_max - self._n))
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
        r"""
        Make this object immutable.
        """
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
        r"""
        Helper function to convert ``h`` to a valid half-edge.

        If the input is invalid, raises an appropriate error.

        TESTS::

            sage: from veerer import Triangulation
            sage: Triangulation("(0,1,~1)")._check_half_edge(0)
            0
            sage: Triangulation("(0,1,~1)")._check_half_edge(-4)
            Traceback (most recent call last):
            ...
            ValueError: half-edge number out of range h=-4
            sage: Triangulation("(0,1,~1)")._check_half_edge(12)
            Traceback (most recent call last):
            ...
            ValueError: half-edge number out of range h=12
            sage: Triangulation("(0,1,~1)")._check_half_edge(1)
            Traceback (most recent call last):
            ...
            ValueError: invalid half-edge h=1; the underlying edges is folded
        """
        if not isinstance(h, numbers.Integral):
            raise TypeError('invalid half-edge {}'.format(h))
        h = int(h)
        if h < 0 or h >= 2 * self._ne:
            raise ValueError(f"half-edge number out of range h={h}")
        if self._vp[h] == -1:
            raise ValueError(f"invalid half-edge h={h}; the underlying edges is folded")
        return h

    def _check_edge(self, e):
        r"""
        Helper function to convert ``e`` to a valid edge.

        If the input is invalid, raises an appropriate error.

        TESTS::

            sage: from veerer import Triangulation
            sage: Triangulation("(0,1,~1)")._check_edge(0)
            0
            sage: Triangulation("(0,1,~1)")._check_edge(-1)
            Traceback (most recent call last):
            ...
            ValueError: edge number out of range e=-1
            sage: Triangulation("(0,1,~1)")._check_edge(2)
            Traceback (most recent call last):
            ...
            ValueError: edge number out of range e=2
        """
        if not isinstance(e, numbers.Integral):
            raise TypeError(f"invalid edge {e}")
        e = int(e)
        if e < 0 or e >= self._ne:
            raise ValueError(f"edge number out of range e={e}")
        return e

    def constellation(self):
        return self

    def to_string(self):
        r"""
        Serialize this constellation as a string.

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

        C._constellation_class = cls
        C._ne = n // 2
        C._vp = vp
        C._fp = fp
        C._half_edges_data = tuple(half_edges_data)
        C._edges_data = tuple(edges_data)
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
        return self._ne != other._ne or self._fp != other._fp or self._half_edges_data != other._half_edges_data or self._edges_data != other._edges_data

    def _cmp_(self, other):
        r"""
        TESTS::

            sage: import itertools
            sage: from veerer import Triangulation
            sage: ts = [Triangulation("(0,1,2)"), Triangulation("(0:1,1:1,2:1)"), Triangulation("(0:1,1:1,2:2)"), Triangulation("(0,1,2)(~0,~1,~2)"), Triangulation("(0,1,2)(~0,~1,~2)"), Triangulation("(0,~0,1)(~1,2,~2)")]
            sage: for t1, t2 in itertools.product(ts, repeat=2):
            ....:     c1 = t1._cmp_(t2)
            ....:     c2 = t2._cmp_(t1)
            ....:     assert c1 == -c2
            ....:     assert (c1 == 0) == (t1 == t2)
        """
        if type(self) is not type(other):
            raise TypeError("can not compare {} with {}".format(type(self).__name__, type(other).__name__))

        c = (self._ne > other._ne) - (self._ne < other._ne)
        if c:
            return c

        c = (self._fp > other._fp) - (self._fp < other._fp)
        if c:
            return c

        c = (self._half_edges_data > other._half_edges_data) - (self._half_edges_data < other._half_edges_data)
        if c:
            return c

        c = (self._edges_data > other._edges_data) - (self._edges_data < other._edges_data)
        return c

    def _richcmp_(self, other, op):
        r"""
        Compare ``self`` and ``other`` according to the operator ``op``.

        EXAMPLES::

            sage: import itertools
            sage: from veerer import Triangulation, VeeringTriangulation

            sage: ts = [Triangulation("(0,1,2)"), Triangulation("(0:1,1:1,2:1)"), Triangulation("(0:1,1:1,2:2)"), Triangulation("(0,1,2)(~0,~1,~2)"), Triangulation("(0,1,2)(~0,~1,~2)"), Triangulation("(0,~0,1)(~1,2,~2)")]
            sage: for t1, t2 in itertools.product(ts, repeat=2):
            ....:     if t1 == t2:
            ....:         assert (t1 <= t2)
            ....:         assert (t1 >= t2)
            ....:         assert not (t1 < t2)
            ....:         assert not (t1 > t2)
            ....:     else:
            ....:         assert (t1 < t2) + (t2 < t1) == 1
            ....:         assert (t1 > t2) + (t2 > t1) == 1
            ....:         assert (t1 < t2) == (t1 <= t2)
            ....:         assert (t1 > t2) == (t1 >= t2)

            sage: vt0 = VeeringTriangulation("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "RRBR")
            sage: vt1 = VeeringTriangulation("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "BRRB")
            sage: (vt0 < vt1) + (vt0 == vt1) + (vt0 > vt1)
            1
            sage: (vt1 < vt0) + (vt1 == vt0) + (vt1 > vt0)
            1
        """
        if type(self) is not type(other):
            raise TypeError("can not compare {} with {}".format(type(self).__name__, type(other).__name__))

        return rich_to_bool(op, self._cmp_(other))

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
            sage: S1.flip(1, BLUE)
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
                T._constellation_class = cls
                T._ne = self._ne
                T._fp = self._fp
                T._vp = self._vp
                T._half_edges_data = self._half_edges_data
                T._edges_data = self._edges_data
                T._mutable = mutable
        else:
            T = cls.__new__(cls)
            T._constellation_class = cls
            T._ne = self._ne
            T._fp = self._fp[:]
            T._vp = self._vp[:]
            T._half_edges_data = tuple(l[:] for l in self._half_edges_data)
            T._edges_data = tuple(l[:] for l in self._edges_data)
            T._mutable = mutable

        T._set_data_pointers()
        return T

    def vertex_permutation(self, copy=True):
        r"""
        Return the permutation encoding the vertices of ``self``.

        Going counterclockwise around vertices makes a permutation of the darts
        whose cycles in its cycle decomposition are in bijection with vertices.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: sphere = Triangulation("(0,1,2)(~0,~2,~1)")
            sage: sphere.vertex_permutation()
            array('i', [5, 2, 1, 4, 3, 0])

        If the triangulation has folded edges, then the vertex permutation is only partial::

            sage: t = Triangulation("(0,1,2)(~0,3,4)")
            sage: t.vertex_permutation()
            array('i', [4, 8, 1, -1, 2, -1, 0, -1, 6, -1])
        """
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

    def previous_at_vertex(self, h, check=True):
        r"""
        Return the half-edge before ``h`` around the corresponding vertex.

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
            h = self._check_half_edge(h)
        return self._fp[self._ep(h)]

    def edge_permutation(self, copy=True):
        r"""
        Return the edge permutation.

        EXAMPLES::

            sage: from veerer import Triangulation

            sage: Triangulation("(0,1,2)(~0,~1,~2)").edge_permutation()
            array('i', [1, 0, 3, 2, 5, 4])
            sage: Triangulation("(0,1,2)").edge_permutation()
            array('i', [0, -1, 2, -1, 4, -1])
        """
        return array('i', [self._ep(h) for h in range(2 * self._ne)])

    def next_in_edge(self, h, check=True):
        r"""
        Return the next half-edge in the edge.
        """
        if check:
            self._check_half_edge(h)
        return self._ep(h)

    def previous_in_edge(self, h, check=True):
        if check:
            self._check_half_edge(h)
        return self._ep(h)

    def face_permutation(self, copy=True):
        r"""
        Return the permutation encoding the faces of ``self``.

        Going counterclockwise around faces makes a permutation of the
        darts whose cycles in its cycle decomposition are in bijection with
        vertices.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: sphere = Triangulation("(0,1,2)(~0,~2,~1)")
            sage: sphere.face_permutation()
            array('i', [2, 5, 4, 1, 0, 3])

        If the triangulation has folded edges, then the face permutation is only partial::

            sage: T = Triangulation("(0,1,2)(~0,3,4)")
            sage: T.face_permutation()
            array('i', [2, 6, 4, -1, 0, -1, 8, -1, 1, -1])
        """
        if copy:
            return self._fp[:]
        else:
            return self._fp

    def next_in_face(self, h, check=True):
        r"""
        Return the half-edge after ``h`` in the corresponding face.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: t = Triangulation("(0,1,2)(~1,3,4)")
            sage: t.next_in_face(0)
            2
            sage: t.next_in_face(2)
            4
            sage: t.next_in_face(4)
            0
            sage: t.next_in_face(1)
            Traceback (most recent call last):
            ...
            ValueError: invalid half-edge h=1; the underlying edges is folded
        """
        if check:
            h = self._check_half_edge(h)
        return self._fp[h]

    def previous_in_face(self, h, check=True):
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
            h = self._check_half_edge(h)
        return self._ep(self._vp[h])

    def half_edges(self):
        r"""
        Iterate through the half-edges of this constellation.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: list(Triangulation("(0,1,2)(~1,3,4)").half_edges())
            [0, 2, 3, 4, 6, 8]
        """
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
        return self._ne + sum(self._vp[i] != -1 for i in range(1, 2 * self._ne, 2))

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

    def folded_half_edges(self):
        r"""
        Iterate through half-edges on a folded edge.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: list(Triangulation("(0,1,2)(~0,~1,~2)").folded_half_edges())
            []
            sage: list(Triangulation("(0,1,2)").folded_half_edges())
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

    @staticmethod
    def _half_edge_string(h):
        r"""
        Helper method to convert the half-edge ``h`` to a string.
        """
        return '~%d' % (h // 2) if h % 2 else '%d' % (h // 2)

    def edges(self):
        r"""
        Return the list of edges as orbits of half-edges.

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

    num_internal_faces = num_faces

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
        Return the connected components as a list of lists of edges.

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: T = Triangulation("(0,1,3)(~0,~1,~3)(2,4,5)(~2,~4,~5)")
            sage: T.connected_components()
            [[0, 1, 3], [2, 4, 5]]

        To construct the triangulation induced on each connected component, one can
        use the method :meth:`subgraph`::

            sage: c0, c1 = T.connected_components()
            sage: T.subgraph(c0)
            Triangulation("(0,1,2)(~0,~1,~2)")
            sage: T.subgraph(c1)
            Triangulation("(0,1,2)(~0,~1,~2)")
        """
        return perm_edge_orbits(self._vp, self._ne)

    def subgraph(self, edges, mutable=False, check=True):
        r"""
        Return the subgraph of this constellation induced on ``edges``.

        The numbering used on the returned subgraph corresponds to
        the order of ``edges`` given as input.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: t = StrebelGraph("(0,1,2)(~0,3,4)(~1,~3,5)(~2,~5,6)(~7,~6,7)")
            sage: t.subgraph([0, 3, 5])
            StrebelGraph("(0,~1,2,~2)(~0,1)")
            sage: t.subgraph([5, 0, 3])  # isomorphic graph
            StrebelGraph("(0,~0,1,~2)(~1,2)")

        Note that the result might not be connected::

            sage: t.subgraph([1, 6])
            StrebelGraph("(0,~0)(1)(~1)")
        """
        if check:
            edges = [self._check_edge(e) for e in edges]
            S = set(edges)
            if len(S) != len(edges):
                raise ValueError('redundant edges')

        ne = len(edges)
        relabel = [-1] * (2 * self._ne)
        half_edges = []
        for i, j in enumerate(edges):
            relabel[2 * j] = 2 * i
            relabel[2 * j + 1] = 2 * i + 1
            half_edges.append(2 * j)
            half_edges.append(2 * j + 1)
        vp = array('i', [-1] * (2 * len(edges)))

        for h in half_edges:
            if self._vp[h] == -1:
                continue
            h_image = self._vp[h]
            while relabel[h_image] == -1:
                h_image = self._vp[h_image]
            vp[relabel[h]] = relabel[h_image]

        half_edges_data = []
        for l in self._half_edges_data:
            half_edges_data.append(array('i', [l[h] for h in half_edges]))
        edges_data = []
        for l in self._edges_data:
            edges_data.append(array('i', [l[e] for e in edges]))

        return self.__class__.from_permutations(vp, None, half_edges_data, edges_data, mutable=mutable, check=True)

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
            yield self.subgraph(comp, mutable=mutable)

    def euler_characteristic(self):
        r"""
        Return the Euler characteristic of this constellation.

        EXAMPLES::

            sage: from veerer import Triangulation, StrebelGraph

        A sphere::

            sage: T = Triangulation("(0,1,2)")
            sage: T.euler_characteristic()
            2

        Disks::

            sage: T = Triangulation("(0:1,~0:1)")
            sage: T.euler_characteristic()
            1
            sage: T = Triangulation("(0:1)")
            sage: T.euler_characteristic()
            1

        A torus::

            sage: T = Triangulation("(0,1,2)(~0,~1,~2)")
            sage: T.euler_characteristic()
            0

        A genus 2 surface::

            sage: T = Triangulation("(0,1,2)(~2,3,4)(~4,5,6)(~6,~0,7)(~7,~1,8)(~8,~3,~5)")
            sage: T.euler_characteristic()
            -2

        A cylinder::

            sage: T = Triangulation("(0,1,2)(~0,3,4)(~1,~2)(~3,~4)", {"~1": 1, "~2": 1, "~3": 1, "~4": 1})
            sage: T.euler_characteristic()
            0

        A pair of pants::

            sage: T = Triangulation("(0,1,2)(~0)(~1)(~2)", {"~0": 1, "~1": 1, "~2": 1})
            sage: T.euler_characteristic()
            -1

        A Strebel graph example::

            sage: sg = StrebelGraph("(0,1)(~0,2,3)(~1,4,5,6)(~2,7,~3,~5)(~4,8,~6)(~7,~8)")
            sage: sg.euler_characteristic()
            0
        """
        return self.num_internal_faces() - self.num_edges() + (self.num_vertices() + self.num_folded_edges())

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
            Triangulation("(0,1,~2)(~0,~1,2)")
            sage: T.swap(2)
            sage: T
            Triangulation("(0,1,2)(~0,~1,~2)")

            sage: T = Triangulation("(0,~5,4)(3,5,6)(1,2,~6)", mutable=True)
            sage: T.swap(0)
            sage: T
            Triangulation("(0,~5,4)(1,2,~6)(3,5,6)")
            sage: T.swap(5)
            sage: T
            Triangulation("(0,5,4)(1,2,~6)(3,~5,6)")

        Also works for veering triangulations::

            sage: from veerer import VeeringTriangulation

            sage: fp = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: cols = "BRBBBRRBBBBR"
            sage: V = VeeringTriangulation(fp, cols, mutable=True)
            sage: V.swap(0)
            sage: V.swap(10)
            sage: V
            VeeringTriangulation("(0,1,~3)(~0,~1,2)(~2,~4,6)(3,4,~5)(5,~9,~7)(~6,8,7)(~8,10,11)(9,~10,~11)", "BRBBBRRBBBBR")

        One can alternatively use ``relabel``::

            sage: T = Triangulation("(0,~5,4)(1,2,~6)(3,5,6)", mutable=True)
            sage: T1 = T.copy()
            sage: T1.swap(5)
            sage: T1.swap(6)
            sage: T2 = T.copy()
            sage: T2.relabel("(5,~5)(6,~6)")
            sage: T1 == T2
            True
        """
        self._assert_mutable()

        if check:
            e = self._check_edge(e)

        vp = self._vp
        ep = self._ep
        fp = self._fp

        h = 2 * e
        H = self._ep(h)
        if h == H:
            return

        # images/preimages by vp
        h_vp = vp[h]
        H_vp = vp[H]
        h_vp_inv = fp[H]
        H_vp_inv = fp[h]
        assert vp[h_vp_inv] == h
        assert vp[H_vp_inv] == H

        # images/preimages by fp
        h_fp = fp[h]
        H_fp = fp[H]
        h_fp_inv = ep(h_vp)
        H_fp_inv = ep(H_vp)
        assert fp[h_fp_inv] == h
        assert fp[H_fp_inv] == H

        fp[h_fp_inv] = H
        fp[H_fp_inv] = h
        vp[h_vp_inv] = H
        vp[H_vp_inv] = h
        fp[h] = H_fp
        fp[H] = h_fp
        vp[h] = H_vp
        vp[H] = h_vp

        for l in self._half_edges_data:
            l[h], l[H] = l[H], l[h]

    def _extra_relabelling(self, p):
        pass

    # TODO: clean documentation
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
            ValueError: immutable Triangulation; use a mutable copy instead

        An example of a flip sequence which forms a loop after non-trivial relabelling::

            sage: T0 = Triangulation("(1,~0,4)(2,~4,~1)(3,~2,5)(~5,~3,0)")
            sage: T = T0.copy(mutable=True)
            sage: T.flip_back(1)
            sage: T.flip_back(3)
            sage: T.flip_back(0)
            sage: T.flip_back(2)
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

        Composing relabellings and permutation composition (from left to right)::

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
        self._assert_mutable()

        if check:
            p = check_relabelling(p, self._ne)

        # TODO: would better be inplace!!
        self._vp = perm_conjugate(self._vp, p)
        self._fp = perm_conjugate(self._fp, p)
        for l in self._half_edges_data:
            perm_on_array(l, l, p, 2 * self._ne)

        for l in self._edges_data:
            perm_on_edge_array(l, l, p, 2 * self._ne)

        self._extra_relabelling(p)
        self._check()

    # TODO: consider listing all quotients by looking at blocks under the monodromy group
    def automorphism_quotient(self, mapping=False, mutable=False, check=True):
        r"""
        Return the quotient under the automorphism group.

        EXAMPLES::

            sage: from veerer import *

        Veering triangulation example::

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,~0)(5,6,~1)(7,~2,8)(9,~3,~6)(10,~7,~4)(11,~5,12)(13,14,~8)(15,~9,16)(17,18,~10)(19,~17,~11)(20,~13,~12)(21,~14,~18)(22,~21,~15)(23,24,~16)(25,~23,~19)(26,~20,~25)(~26,~24,~22)", "RBBRBRBRRBRBBRBBRRBRRRBBRRB")
            sage: len(vt.automorphisms())
            2
            sage: qvt = vt.automorphism_quotient()
            sage: qvt
            VeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)(~2,8,7)(~3,~6,9)(~4,10,~7)(~5,12,11)(~8,13,~12)(~10,14,~11)", "RBBRBRBRRBRBBRR")
            sage: (vt.stratum(), qvt.stratum())  # optional - surface_dynamics
            (H_4(2^3), Q_1(1^3, -1^3))

            sage: vt.automorphism_quotient(mapping=True)
            (VeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)(~2,8,7)(~3,~6,9)(~4,10,~7)(~5,12,11)(~8,13,~12)(~10,14,~11)", "RBBRBRBRRBRBBRR"),
             array('i', [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 18, 20, 21, 22, 23, 24, 25, 26, 26, 25, 24, 13, 12, 7, 6, 28, 28, 23, 22, 21, 20, 17, 16, 11, 10, 3, 2, 8, 9, 1, 0, 15, 14, 5, 4]))

        Strebel graph example::

            sage: sg = StrebelGraph("(0,~0,~1)(1,2,~2)")
            sage: sg.automorphism_quotient()
            StrebelGraph("(0,~0,1)")

        TESTS::

            sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,7,8)(~4,~7,9)(~6,10,11)(~8,12,13)(~9,14,15)(~10,16,17)(~11,18,~17)(~12,19,~18)(~14,20,~16)(0:1)(~5:1)(~13:1)(~15:1)(~19:1)(~20:1)", "RBBBRRBRBBRRBRBRBBBRR")
            sage: vt.automorphism_quotient()
            VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,7,8)(~4,~7,~6)(~8,9,10)(0:1)(~5:1)(~10:1)", "RBBBRRBRBBR")
        """
        return self.quotient(perms_orbits(self.automorphisms()), mapping, mutable, check)

    def quotient(self, blocks, mapping=False, mutable=False, check=True):
        if check:
            if not all(blocks):
                raise ValueError("each block must be non empty")
            blocks = [[self._check_half_edge(h) for h in block] for block in blocks]
            half_edges = set().union(*blocks)
            if half_edges != set(self.half_edges()):
                raise ValueError("invalid blocks")
            for block in blocks:
                for l in self._half_edges_data:
                    if len(set(l[h] for h in block)) != 1:
                        raise ValueError("block must be constant on half-edges data")
                for l in self._edges_data:
                    if len(set(l[h // 2] for h in block)) != 1:
                        raise ValueError("block must be constant on edges data")

        half_edge_to_block = [-1] * (2 * self._ne)
        for i, block in enumerate(blocks):
            for j in block:
                half_edge_to_block[j] = i

        if check:
            for block in blocks:
                if len(set(half_edge_to_block[self._vp[h]] for h in block)) != 1:
                    raise ValueError("invalid blocks")
                if len(set(half_edge_to_block[self._fp[h]] for h in block)) != 1:
                    raise ValueError("invalid blocks")

        ne = 0
        block_relabelling = {-1: -1}
        for e in range(self._ne):
            i = half_edge_to_block[2 * e]
            if i in block_relabelling:
                continue
            block_relabelling[i] = 2 * ne
            if self._vp[2 * e + 1] != -1:
                ii = half_edge_to_block[2 * e + 1]
                if ii in block_relabelling:
                    assert i == ii  # folding
                else:
                    block_relabelling[ii] = 2 * ne + 1
            ne += 1

        vp = array('i', [-1] * (2 * ne))
        fp = array('i', [-1] * (2 * ne))
        half_edges_data = [array('i', [0] * (2 * ne)) for _ in self._half_edges_data]
        edges_data = [array('i', [0] * ne) for _ in self._edges_data]
        for i, block in enumerate(blocks):
            h = block[0]
            ii = half_edge_to_block[self._vp[h]]
            vp[block_relabelling[i]] = block_relabelling[ii]

            ii = half_edge_to_block[self._fp[h]]
            fp[block_relabelling[i]] = block_relabelling[ii]

            for ldest, lsrc in zip(half_edges_data, self._half_edges_data):
                ldest[block_relabelling[i]] = lsrc[h]
            for ldest, lsrc in zip(edges_data, self._edges_data):
                ldest[block_relabelling[i] // 2] = lsrc[h // 2]

        quotient = self.from_permutations(vp, fp, half_edges_data, edges_data, mutable, check)
        return (quotient, array('i', [block_relabelling[half_edge_to_block[h]] for h in range(2 * self._ne)])) if mapping else quotient

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
        fp_new = array('i', [-1] * (2 * self._ne))
        last = edge_relabelling_from(relabelling, fp_new, self._fp, self._ne * 2, root, 0)
        assert fp_new == perm_conjugate(self._fp, relabelling), (fp_new, perm_conjugate(self._fp, relabelling))
        if last // 2 != self._ne:
            raise ValueError("non-connected constellation")
        return relabelling

    def automorphisms(self):
        r"""
        Return the list of automorphisms of this constellation.

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
            sage: len(s.automorphisms())
            2
            sage: len(f.automorphisms())
            2

        A non-connected example::

            sage: t = Triangulation("(0,1,3)(2,4,~4)(~2,5,~5)(6,7,8)")
            sage: len(t.automorphisms())
            36

        TESTS::

            sage: examples = []
            sage: examples.append(Triangulation("(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"))
            sage: examples.append(Triangulation("(0,8,~7)(1,9,~0)(2,10,~1)(3,11,~2)(4,12,~3)(5,13,~4)(6,14,~5)(7,15,~6)"))
            sage: examples.append(Triangulation("(0,1,2)", boundary="(~0:1)(~1:1)(~2:1)"))
            sage: examples.append(Triangulation("(0,1,3)(2,4,~4)(~2,5,~5)(6,7,8)"))

            sage: examples.append(StrebelGraph("(0,3,7,~6,~2,1)(2,5,~4,~3,~1,~0)(4,8,~5)(6,~8,~7)"))
            sage: for G in examples:
            ....:     H = G.copy(mutable=True)
            ....:     for a in G.automorphisms():
            ....:         assert H == G
            ....:         H.relabel(a)
            ....:         assert H == G, (G, H, a)
        """
        best_relabellings = self.best_relabelling(return_all=True)[0]
        p0 = perm_invert(best_relabellings[0])
        return [perm_compose(p, p0) for p in best_relabellings]

    def automorphism_gens(self):
        return self.automorphisms()

    def best_relabelling(self, return_all=False):
        r"""
        Return a pair ``(r, data)`` where ``r`` is a relabelling that
        brings this constellation to the canonical one.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation, StrebelGraph
            sage: from veerer.permutation import perm_random_centralizer

            sage: examples = []
            sage: triangles = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: examples.append(Triangulation(triangles, mutable=True))
            sage: examples.append(Triangulation("(0,1,3)(2,4,~4)(~2,5,~5)(6,7,8)", mutable=True))
            sage: fp = "(0,~1,2)(~0,1,~3)(4,~5,3)(~4,6,~2)(7,~6,8)(~7,5,~9)(10,~11,9)(~10,11,~8)"
            sage: cols = "BRBBBRRBBBBR"
            sage: examples.append(VeeringTriangulation(fp, cols, mutable=True))
            sage: fp = "(0,16,~15)(1,19,~18)(2,22,~21)(3,21,~20)(4,20,~19)(5,23,~22)(6,18,~17)(7,17,~16)(8,~1,~23)(9,~2,~8)(10,~3,~9)(11,~4,~10)(12,~5,~11)(13,~6,~12)(14,~7,~13)(15,~0,~14)"
            sage: cols = "RRRRRRRRBBBBBBBBBBBBBBBB"
            sage: examples.append(VeeringTriangulation(fp, cols, mutable=True))
            sage: examples.append(StrebelGraph("(0,6,~5,~3,~1,4,~4,2,~2)(1)(3,~0)(5)(~6)", mutable=True))
            sage: examples.append(StrebelGraph("(0,6,~5,~3,~1,4,~4:3,2,~2:3)(1:2)(3:2,~0)(5:2)(~6)", mutable=True))

            sage: for G in examples:
            ....:     print(G)
            ....:     r, fp, half_edges_data, edges_data = G.best_relabelling()
            ....:     for _ in range(10):
            ....:         p = perm_random_centralizer(G.edge_permutation())
            ....:         G.relabel(p)
            ....:         r2, fp2, half_edges_data2, edges_data2 = G.best_relabelling()
            ....:         assert fp2 == fp, G
            ....:         assert half_edges_data2 == half_edges_data, (G, half_edges_data2, half_edges_data)
            ....:         assert edges_data2 == edges_data, (G, edges_data2, edges_data)
            Triangulation("(0,~1,2)(~0,1,~3)(~2,~4,6)(3,4,~5)(5,~9,~7)(~6,8,7)(~8,~10,11)(9,10,~11)")
            Triangulation("(0,1,3)(2,4,~4)(~2,5,~5)(6,7,8)")
            VeeringTriangulation("(0,~1,2)(~0,1,~3)(~2,~4,6)(3,4,~5)(5,~9,~7)(~6,8,7)(~8,~10,11)(9,10,~11)", "BRBBBRRBBBBR")
            VeeringTriangulation("(0,16,~15)(~0,~14,15)(1,19,~18)(~1,~23,8)(2,22,~21)(~2,~8,9)(3,21,~20)(~3,~9,10)(4,20,~19)(~4,~10,11)(5,23,~22)(~5,~11,12)(6,18,~17)(~6,~12,13)(7,17,~16)(~7,~13,14)", "RRRRRRRRBBBBBBBBBBBBBBBB")
            StrebelGraph("(0,6,~5,~3,~1,4,~4,2,~2)(~0,3)(1)(5)(~6)")
            StrebelGraph("(0,6,~5,~3,~1,4,~4:3,2,~2:3)(~0,3:2)(1:2)(5:2)(~6)")
        """
        ne = self._ne
        n = 2 * ne

        if not self.is_connected():
            # each component is labelled with consecutive half-edge labels
            # we use canonical labels for each of them, and then use a total ordering on the components
            components = {}
            for cc in self.connected_components():
                # TODO: set check to False
                comp = self.subgraph(cc, check=True)
                relabelling_best, fp_best, half_edges_data_best, edges_data_best = comp.best_relabelling(return_all=return_all)

                comp_hashable = [fp_best.tobytes()]
                comp_hashable.extend(data.tobytes() for data in half_edges_data_best)
                comp_hashable.extend(data.tobytes() for data in edges_data_best)
                comp_hashable = tuple(comp_hashable)
                if comp_hashable not in components:
                    components[comp_hashable] = []
                if return_all:
                    data = (cc, relabelling_best[0], relabelling_best, fp_best, half_edges_data_best, edges_data_best)
                else:
                    data = (cc, relabelling_best, None, fp_best, half_edges_data_best, edges_data_best)

                components[comp_hashable].append(data)

            relabelling_best = array('i', [-1] * n)
            fp_best = array('i', [-1] * n)
            half_edges_data_best = array('i', [0] * n)
            edges_data_best = array('i', [0] * n)

            shift = 0
            for comp_hashable in sorted(components):
                value = components[comp_hashable]
                for comp, comp_relabelling_best, _, _, _, _ in components[comp_hashable]:
                    # NOTE: elements in comp are edges, not half-edges
                    for i, j in enumerate(comp):
                        i0 = comp_relabelling_best[2 * i]
                        i1 = comp_relabelling_best[2 * i + 1]
                        relabelling_best[2 * j] = shift + i0
                        relabelling_best[2 * j + 1] = shift + i1
                    shift += 2 * len(comp)

            fp_best = perm_conjugate(self._fp, relabelling_best)
            half_edges_data_best = tuple(l[:] for l in self._half_edges_data)
            for ldest, lsrc in zip(half_edges_data_best, self._half_edges_data):
                perm_on_array(ldest, lsrc, relabelling_best, n)
            edges_data_best = tuple(l[:] for l in self._edges_data)
            for ldest, lsrc in zip(edges_data_best, self._edges_data):
                perm_on_edge_array(ldest, lsrc, relabelling_best, n)

            if not return_all:
                return (relabelling_best, fp_best, half_edges_data_best, edges_data_best)

            relabellings = []
            for oc in itertools.product(*[itertools.permutations(components[comp_hashable]) for comp_hashable in sorted(components)]):
                # run through all permutations of isomorphic components
                comps = [data[0] for isom_comps in oc for data in isom_comps]
                for comp_relabellings in itertools.product(*[data[2] for isom_comps in oc for data in isom_comps]):
                    # run through products available relabellings
                    relabelling = array('i', [-1] * n)
                    shift = 0
                    for comp, comp_relabelling in zip(comps, comp_relabellings):
                        # NOTE: elements in comp are edges, not half-edges
                        for i, j in enumerate(comp):
                            i0 = comp_relabelling[2 * i]
                            i1 = comp_relabelling[2 * i + 1]
                            relabelling[2 * j] = shift + i0
                            relabelling[2 * j + 1] = shift + i1
                        shift += 2 * len(comp)
                    relabellings.append(relabelling)

            return (relabellings, fp_best, half_edges_data_best, edges_data_best)

        else:
            # connected case
            fp = self._fp
            half_edges_data = self._half_edges_data
            edges_data = self._edges_data
            relabellings = []

            relabelling_new = array('i', [-1] * n)
            relabelling_best = array('i', [-1] * n)
            fp_new = array('i', [-1] * n)
            fp_best = array('i', [-1] * n)
            half_edges_data_new = tuple(l[:] for l in half_edges_data)
            half_edges_data_best = tuple(l[:] for l in half_edges_data)
            edges_data_new = tuple(l[:] for l in edges_data)
            edges_data_best = tuple(l[:] for l in edges_data)
            k_half_edges = len(half_edges_data)
            k_edges = len(edges_data)

            half_edges = self.half_edges()
            edge_relabelling_from(relabelling_best, fp_best, self._fp, 2 * ne, next(half_edges), 0)
            for i in range(k_half_edges):
                perm_on_array(half_edges_data_best[i], half_edges_data[i], relabelling_best, 2 * ne)
            for i in range(k_edges):
                perm_on_edge_array(edges_data_best[i], edges_data[i], relabelling_best, 2 * ne)

            if return_all:
                relabellings.append(relabelling_best[:])

            for start_half_edge in half_edges:
                # reinitialize relabelling_new as intended by edge_relabelling_from
                for i in range(n):
                    relabelling_new[i] = fp_new[i] = -1
                end_image = edge_relabelling_from(relabelling_new, fp_new, self._fp, n, start_half_edge, 0)
                assert end_image == 2 * ne, (end_image, ne)
                assert sum(x == -1 for x in fp_new) == sum(x == -1 for x in self._fp)
                assert all(x != -1 for x in relabelling_new)

                c = 0
                if fp_new < fp_best:
                    # no need to compare anything else
                    c = -1
                elif fp_new > fp_best:
                    # no need to go further
                    c = 1
                    continue

                for i in range(k_half_edges):
                    perm_on_array(half_edges_data_new[i], half_edges_data[i], relabelling_new, 2 * ne)
                    if not c:
                        if half_edges_data_new[i] < half_edges_data_best[i]:
                            c = -1
                        elif half_edges_data_new[i] > half_edges_data_best[i]:
                            c = 1
                            break
                if c == 1:
                    continue

                for i in range(k_edges):
                    perm_on_edge_array(edges_data_new[i], edges_data[i], relabelling_new, 2 * ne)
                    if not c:
                        if edges_data_new[i] < edges_data_best[i]:
                            c = -1
                        elif edges_data_new[i] > edges_data_best[i]:
                            c = 1
                            break
                if c == 1:
                    continue

                # at this stage either c=0 and relabelling is identical or c=-1 and we found something better
                if c == -1:
                    fp_best, fp_new = fp_new, fp_best
                    relabelling_best, relabelling_new = relabelling_new, relabelling_best
                    half_edges_data_best, half_edges_data_new = half_edges_data_new, half_edges_data_best
                    edges_data_best, edges_data_new = edges_data_new, edges_data_best
                    if return_all:
                        relabellings.clear()
                        relabellings.append(relabelling_best[:])
                elif return_all:
                    assert c == 0
                    relabellings.append(relabelling_new[:])

            return (relabellings, fp_best, half_edges_data_best, edges_data_best) if return_all else (relabelling_best, fp_best, half_edges_data_best, edges_data_best)

    # TODO: expand and clean documentation
    def set_canonical_labels(self, mapping=False):
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
            sage: T._check()
            sage: T.set_canonical_labels()
            sage: T
            Triangulation("(0,1,2)(~0,~2,3)(~1,4,5)(~3,6,7)(~4,8,~5)(~6,9,~7)(~8,10,11)(~9,~11,~10)")
            sage: T._check()
        """
        self._assert_mutable()

        r, fp_best, half_edges_data_best, edges_data_best = self.best_relabelling()
        self._fp = fp_best
        self._vp = perm_conjugate(self._vp, r)
        self._half_edges_data = half_edges_data_best
        self._edges_data = edges_data_best
        self._set_data_pointers()
        if mapping:
            return r

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
            sage: T.is_isomorphic(T2)
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
        Return whether ``self`` is isomorphic to ``other``.

        INPUT:

        - ``other`` - a constellation

        - ``certificate`` -- optional boolean (default ``False``), whether to
           additionally return the relabelling when ``self`` and ``other`` are
           isomorphic

        EXAMPLES::

            sage: from veerer import Triangulation
            sage: sphere = Triangulation("(0,1,2)(~0,~2,~1)")
            sage: sphere2 = Triangulation("(0,2,1)(~0,~1,~2)")
            sage: torus = Triangulation("(0,1,2)(~0,~1,~2)")
            sage: sphere.is_isomorphic(sphere2)
            True
            sage: sphere.is_isomorphic(torus)
            False

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

        r1, fp1, half_edges_data1, edges_data1 = self.best_relabelling()
        r2, fp2, half_edges_data2, edges_data2 = other.best_relabelling()

        if fp1 != fp2 or half_edges_data1 != half_edges_data2 or edges_data1 != edges_data2:
            return (False, None) if certificate else False
        elif certificate:
            return (True, perm_compose(r1, perm_invert(r2)))
        else:
            return True

    def is_isomorphic_to(self, *args, **kwds):
        r"""
        Deprecated function.

        TESTS::

            sage: from veerer import Triangulation
            sage: sphere = Triangulation("(0,1,2)(~0,~2,~1)")
            sage: torus = Triangulation("(0,1,2)(~0,~1,~2)")
            sage: sphere.is_isomorphic_to(torus)
            doctest:warning
            ...
            UserWarning: is_isomorphic_to is deprecated; use .is_isomorphic() instead
            False
            sage: sphere.is_isomorphic_to(torus, True)
            (False, None)
        """
        import warnings
        warnings.warn("is_isomorphic_to is deprecated; use .is_isomorphic() instead")
        return self.is_isomorphic(*args, **kwds)
