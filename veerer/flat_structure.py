r"""
Flat structures on veering triangulations and Strebel graphs.
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2018-2024 Vincent Delecroix
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

import copy

from sage.structure.sequence import Sequence
from sage.structure.element import Vector
from sage.categories.rings import Rings
from sage.categories.fields import Fields
from sage.rings.all import ZZ, QQ, AA, RDF, NumberField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.modules.free_module import VectorSpace, FreeModule
from sage.modules.free_module_element import vector

from .constants import BLUE, RED, PURPLE, GREEN, LEFT, RIGHT, HORIZONTAL, VERTICAL
from .constellation import Constellation
from .permutation import perm_cycles, perm_check, perm_init, perm_conjugate, perm_on_list, perm_on_edge_list
from .triangulation import Triangulation
from .veering_triangulation import VeeringTriangulation
from .misc import flipper_edge, flipper_edge_perm, flipper_nf_to_sage, flipper_nf_element_to_sage, det2, flipper_face_edge_perms

_Rings = Rings()
_Fields = Fields()


def slope(x, y):
    r"""
    Return the slope of a 2d vector ``v``.

    EXAMPLES::

        sage: from veerer.constants import RED, BLUE, PURPLE, GREEN  # random output due to deprecation warnings from realalg
        sage: from veerer.flat_structure import slope

        sage: slope(1, 0) == PURPLE
        True
        sage: slope(0, 1) == GREEN
        True
        sage: slope(1, 1) == slope(-1 ,-1) == RED
        True
        sage: slope(1, -1) == slope(1, -1) == BLUE
        True
    """
    if x.is_zero() and y.is_zero():
        raise ValueError("zero vector")
    if x.is_zero():
        return GREEN
    elif y.is_zero():
        return PURPLE
    elif x * y > 0:
        return RED
    else:
        return BLUE


class FlatStructure:
    r"""
    Abstract class to handle coordinates on either veering triangulation or
    Strebel graph.
    """
    def _constellation_class_init(self):
        bases = self.__class__.__bases__
        if len(bases) != 2 or bases[0] != FlatStructure or not issubclass(bases[1], Constellation):
            raise TypeError("invalid class")
        self._constellation_class = bases[1]

    def __init__(self, *args, mutable=False, check=False):
        self._constellation_class_init()
        if len(args) < 3:
            raise ValueError("require at least three arguments")
        constellation_args = args[:-2]
        x = args[-2]
        y = args[-1]
        if len(constellation_args) == 1:
            arg = constellation_args[0]
            if not isinstance(arg, VeeringTriangulation):
                # guess colors based on input
                if not isinstance(arg, Triangulation):
                    arg = Triangulation(arg)
                colouring = arg.colouring_from_xy(x, y)
                vt = VeeringTriangulation(arg, colouring)
                constellation_args = (vt,)
        self._constellation_class.__init__(self, *constellation_args, mutable=mutable, check=False)

        if not isinstance(x, Vector) or not isinstance(y, Vector):
            S = Sequence(list(x) + list(y))
            base_ring = S.universe()
            if base_ring not in _Rings:
                raise ValueError("invalid coordinates: x={} y={} with universe={}".format(x, y, base_ring))
            if base_ring not in _Fields:
                base_ring = base_ring.fraction_field()
            x = vector(list(map(base_ring, x)))
            y = vector(list(map(base_ring, y)))
        elif x.parent() != y.parent():
            V = x.common_parent(y)
            x = V(x)
            y = V(y)
            base_ring = V.base_ring()

        self._x = x
        self._y = y

        if not mutable:
            self._x.set_immutable()
            self._y.set_immutable()
        else:
            if not x.is_mutable():
                self._x = copy.copy(self._x)
            if not y.is_mutable():
                self._y = copy.copy(self._y)

        if check:
            self._check()

    def constellation(self, mutable=False):
        return Constellation.copy(self, mutable, cls=self._constellation_class)


class FlatVeeringTriangulation(FlatStructure, VeeringTriangulation):
    r"""
    A veering triangulation with a flat structure.

    EXAMPLES::

        sage: from veerer import FlatVeeringTriangulation

        sage: x = (1, 2, 1)
        sage: y = (2, 1, 1)
        sage: FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", x, y)
        FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", (1, 2, 1), (2, 1, 1))

    TESTS::

        sage: from veerer import Triangulation, FlatVeeringTriangulation
        sage: T = Triangulation("(0,1,2)(3,4,~0)(5,6,~1)")
        sage: fl = FlatVeeringTriangulation(T, [47, 27, 74, 22, 69, 61, 34], [51, 67, 16, 79, 28, 31, 36], mutable=True)
        sage: fl.relabel('(1,0)(3,5,4,6)')
        sage: fl
        FlatVeeringTriangulation("(0,2,1)(~0,4,3)(~1,5,6)", "RBRBRRR", (27, 47, 74, 34, 61, 22, 69), (67, 51, 16, 36, 31, 79, 28))
    """
    __slots__ = ['_x', '_y']

    def base_ring(self):
        return self._x.base_ring()

    def _check(self, error=ValueError):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR")
            sage: assert T.is_core()
            sage: F = T.flat_structure_min()
            sage: F._check()
        """
        self._constellation_class._check(self, error)
        x = self._x
        y = self._y
        if not isinstance(x, Vector) or not isinstance(y, Vector) or len(x) != self._ne or len(y) != self._ne:
            raise error("invalid coordinates")
        if self._mutable != x.is_mutable() or self._mutable != y.is_mutable():
            raise error("incoherent mutability state: self._mutable={}, x.is_mutable()={}, y.is_mutable()={}".format(self._mutable, x.is_mutable(), y.is_mutable()))

        self._set_subspace_constraints(lambda c: self._constraint_check(c, error), x, VERTICAL)
        self._set_subspace_constraints(lambda c: self._constraint_check(c, error), y, HORIZONTAL)

    def __str__(self):
        r"""
        Return a string representation.
        """
        cls_name = self._constellation_class.__name__
        s = str(self._constellation_class.__str__(self))
        i = s.find('(')
        return 'Flat' + s[:i] + s[i:-1] + ', ' + str(self._x) + ', ' + str(self._y) + ')'

    @classmethod
    def from_coloured_triangulation(cls, T):
        r"""
        Construct a flat triangulation associated to a given coloured triangulation.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: FlatVeeringTriangulation.from_coloured_triangulation(T)
            FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", (1, 2, 1), (2, 1, 1))
        """
        return T.flat_structure_min()

    def boshernitzan_criterion(self):
        r"""
        """
        raise NotImplementedError

    @classmethod
    def from_flipper_pseudo_anosov(cls, h):
        r"""
        Construct the flat structure from a pseudo-Anosov homeomorphism.

        EXAMPLES::

            sage: from flipper import *  # optional - flipper
            sage: from veerer import *

            sage: T = flipper.load('SB_4')  # optional - flipper
            sage: h = T.mapping_class('s_0S_1s_2S_3s_1S_2').canonical()     # optional - flipper
            sage: F = FlatVeeringTriangulation.from_flipper_pseudo_anosov(h)  # optional - flipper
            sage: F                                                         # optional - flipper
            FlatVeeringTriangulation(Triangulation("(0,4,~1)(1,5,3)(2,~0,~3)(~5,~4,~2)"), [(-2, -1), (-2*a + 4, a - 1), (-2*a + 4, a - 1), (2*a - 2, -a + 2), (2*a - 2, -a + 2), (-2, -1), (-2, -1), (2*a - 2, -a + 2), (2*a - 2, -a + 2), (-2*a + 4, a - 1), (-2*a + 4, a - 1), (-2, -1)])

        The flipper and veerer triangulations carry the same edge labels::

            sage: F.to_veering_triangulation()         # optional - flipper
            VeeringTriangulation("(0,4,~1)(1,5,3)(2,~0,~3)(~5,~4,~2)", "RBBBBR")
            sage: h.source_triangulation   # optional - flipper
            [(~5, ~4, ~2), (~3, 2, ~0), (~1, 0, 4), (1, 5, 3)]
        """
        Fh = h.flat_structure()
        Th = Fh.triangulation
        n = 3 * Th.num_triangles # number of half edges

        fp, ep = flipper_face_edge_perms(Th)
        T = Triangulation.from_face_edge_perms(fp, ep)

        # extract flat structure
        x = next(iter(Fh.edge_vectors.values())).x
        K = flipper_nf_to_sage(x.field)
        V = VectorSpace(K, 2)
        # translate into Sage number field
        Vec = {flipper_edge(Th,e): V((flipper_nf_element_to_sage(v.x, K),
                               flipper_nf_element_to_sage(v.y, K)))
                  for e,v in Fh.edge_vectors.items()}
        vectors = [Vec[i] for i in range(n)]

        return FlatVeeringTriangulation(T, vectors, K)

    def __repr__(self):
        return str(self)

    def copy(self, mutable=None, cls=None):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR")
            sage: F = T.flat_structure_min()
            sage: F.copy()
            FlatVeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR", (1, 1, 2, 2), (1, 2, 1, 1))
            sage: F.copy(mutable=True)._check()
            sage: F.copy(mutable=False)._check()
        """
        if mutable is None:
            mutable = self._mutable

        if cls is None:
            cls = self.__class__

        if cls is self.__class__ and (not self._mutable and not mutable):
            # avoid copies of immutable objects
            return self

        if cls is not self.__class__:
            return super().copy(mutable, cls)

        F = self._constellation_class.copy(self, mutable=True, cls=self.__class__)
        F._constellation_class = self._constellation_class
        F._x = self._x[:]
        F._y = self._y[:]
        if not mutable:
            F._x.set_immutable()
            F._y.set_immutable()
        return F

    def flat_triangle(self, h, x_start=0, y_start=0, sign=1, check=True):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR")
            sage: F = T.flat_structure_min()
            sage: F.flat_triangle(0)
            [(0, 0), (1, -1), (2, 1), (0, 0)]
            sage: F.flat_triangle(0, sign=-1)
            [(0, 0), (-1, 1), (-2, -1), (0, 0)]
        """
        if check:
            h = self._check_half_edge(h)
        V = FreeModule(self._x.base_ring(), 2)
        fp = self._fp
        x = x_start
        y = y_start
        pts = [V((x, y))]
        col = self.edge_colour(h // 2)
        for _ in range(3):
            x += sign * self._x[h // 2]
            if col == RED:
                y += sign * self._y[h // 2]
            elif col == BLUE:
                y -= sign * self._y[h // 2]
            pts.append(V((x, y)))
            hh = fp[h]
            ccol = self.edge_colour(hh // 2)
            if col != BLUE or ccol != RED:
                sign *= -1
            h = hh
            col = ccol
        assert pts[0] == pts[-1]
        return pts

    def vectors(self):
        ans, oris = self.is_abelian(certificate=True)
        vecs = [None] * (2 * self._ne)
        for a, b, c in self.triangles():
            if ans:
                t = self.flat_triangle(a, sign=(1 if oris[a] else -1))
            else:
                t = self.flat_triangle(a)
            vecs[a] = t[1] - t[0]
            vecs[b] = t[2] - t[1]
            vecs[c] = t[3] - t[2]
        return vecs

    def is_delaunay(self):
        for e in self.backward_flippable_edges(self):
            a, _, _, d = self.square_about_half_edge(2 * e)
            a //= 2
            d //= 2
            if self._x[a] + self._x[d] < self._y[e]:
                return False
        for e in self.forward_flippable_edges(self):
            a, _, _, d = self.square_about_half_edge(2 * e)
            a //= 2
            d //= 2
            if self._y[a] + self._y[d] < self._x[e]:
                return False
        return True

    def delaunay_flip_sequence(self):
        r"""
        Return the list of backward and forward flips to be performed in order
        to turn this flat structure into its Delaunay triangulation.

        EXAMPLES::

            sage: from veerer import FlatVeeringTriangulation
            sage: fl = FlatVeeringTriangulation("(0,3,4)(~0,1,2)(~1,5,6)", "BRRRRRB", (47, 27, 74, 22, 69, 61, 34), (51, 67, 16, 79, 28, 31, 36))
        """
        backward_flips = []
        state = self.copy(mutable=True)
        todo_backward = set(state.backward_flippable_edges())
        todo_forward = set(state.forward_flippable_edges())
        while todo_backward:
            e = todo_backward.pop()
            a, b, c, d = state.square_about_half_edge(2 * e)
            a //= 2
            b //= 2
            c //= 2
            d //= 2
            if state._x[a] + state._x[d] < state._y[e]:
                state.flip_back(e)
                col = state.edge_colour(e)
                backward_flips.append((e, col))
                # TODO: depending on the colour col we only have
                # two possible backward flippable edges
                if state.is_backward_flippable(a):
                    todo_backward.add(a)
                if state.is_backward_flippable(b):
                    todo_backward.add(b)
                if state.is_backward_flippable(c):
                    todo_backward.add(c)
                if state.is_backward_flippable(d):
                    todo_backward.add(d)

        forward_flips = []
        while todo_forward:
            e = todo_forward.pop()
            a, b, c, d = state.square_about_half_edge(2 * e)
            a //= 2
            b //= 2
            c //= 2
            d //= 2
            if state._y[a] + state._y[d] < state._x[e]:
                state.flip(e)
                col = state.edge_colour(e)
                forward_flips.append((e, col))
                # TODO: depending on the colour col we only have
                # two possible forward flippable edges
                if state.is_forward_flippable(a):
                    todo_forward.add(a)
                if state.is_forward_flippable(b):
                    todo_forward.add(b)
                if state.is_forward_flippable(c):
                    todo_forward.add(c)
                if state.is_forward_flippable(d):
                    todo_forward.add(d)

        return backward_flips, forward_flips

    def to_pyflatsurf(self):
        ans, oris = self.is_abelian(certificate=True)
        if not ans:
            raise ValueError("pyflatsurf only works with translation surfaces")
        from pyflatsurf.factory import make_surface
        from pyflatsurf.sage_conversion import make_vectors
        verts = [(i+1 if i >=0 else i for i in c) for c in perm_cycles(self._vp, True, self._n)]
        vectors = makeVectors((x[e], y[e]) for e in range(self._ne))
        return make_surface(verts, vectors)

    def layout(self):
        r"""
        Return a layout for this flat veering triangulation that could be used for
        fine tuned plots.

        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR")
            sage: T.flat_structure_min().layout()
            FlatVeeringTriangulationLayout(FlatVeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR", (1, 1, 2, 2), (1, 2, 1, 1)), [])
        """
        from .layout import FlatVeeringTriangulationLayout
        return FlatVeeringTriangulationLayout(self)

    def plot(self, *args, **kwds):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR")
            sage: F = T.flat_structure_min()
            sage: F.plot()  # random - matplotlib warnings
            Graphics object consisting of ... graphics primitives
        """
        layout = self.layout()
        layout.greedy_gluing()
        return layout.plot(*args, **kwds)

    def flip(self, e, col=None, check=True):
        r"""
        Flip the edge ``e``.

        EXAMPLES::

            sage: from veerer import Triangulation, FlatVeeringTriangulation, RIGHT, LEFT
            sage: fl = FlatVeeringTriangulation("(0,1,2)(3,4,~0)(5,6,~1)", (47, 27, 74, 22, 69, 61, 34), (51, 67, 16, 79, 28, 31, 36), mutable=True)
            sage: fl.flip(2)
            sage: fl.flip(4)
            sage: fl.flip(0)
            sage: fl
            FlatVeeringTriangulation("(0,1,4)(~0,3,2)(~1,5,6)", "RRBRBRB", (2, 27, 20, 22, 25, 61, 34), (197, 67, 118, 79, 130, 31, 36))

            sage: fl = FlatVeeringTriangulation("(0,1,2)(3,4,~0)(5,6,~1)", (47,  27, 74, 22, 69, 61, 34,), (51, 67, 16, 79, 28, 31, 36))
            sage: fl.flip(1)
            Traceback (most recent call last):
            ...
            ValueError: immutable flat veering triangulation; use a mutable copy instead

            sage: fl = FlatVeeringTriangulation("(0, 1, 2)", (13, 21, 8), (8, 3, 5), mutable=True)
            sage: fl.flip(1)
            sage: fl
            FlatVeeringTriangulation("(0,2,1)", "RRB", (13, 5, 8), (8, 13, 5))
        """
        if check:
            if not self._mutable:
                raise ValueError("immutable flat veering triangulation; use a mutable copy instead")

            e = self._check_edge(e)
            if not self.is_forward_flippable(e):
                raise ValueError("invalid edge e={} for forward flip".format(e))

        h = 2 * e
        H = self._ep(h)

        # x<----------x
        # |     a    ^^
        # |         / |
        # |        /  |
        # |       /   |
        # |b    e/   d|
        # |     /     |
        # |    /      |
        # |   /       |
        # |  /        |
        # | /         |
        # v/    c     |
        # x---------->x
        a, b, c, d = self.square_about_half_edge(h)
        ea = a // 2
        eb = b // 2
        ec = c // 2
        ed = d // 2

        assert self._x[e] == self._x[ea] + self._x[eb] == self._x[ec] + self._x[ed]
        assert self._y[e] == abs(self._y[ea] - self._y[eb]) == abs(self._y[ec] - self._y[ed])

        if self._x[ea] > self._x[ed]:
            self._x[e] = self._x[ea] - self._x[ed]
            if col is not None:
                assert col == BLUE
            col = BLUE
        elif self._x[ea] < self._x[ed]:
            self._x[e] = self._x[ed] - self._x[ea]
            if col is not None:
                assert col == RED
            col = RED
        else:
            # equality
            self._x[e] = self._x[ea] - self._x[ed]
            if col is not None:
                assert col == GREEN
            col = GREEN

        self._y[e] = self._y[ea] + self._y[ed]

        self._constellation_class.flip(self, e, col, check=True)

        if check:
            self._check()

    def flip_back(self, e, col=None, check=True):
        r"""
        Flip back the edge ``e``.

        EXAMPLES::

            sage: from veerer import Triangulation, FlatVeeringTriangulation, RIGHT, LEFT
            sage: fl = FlatVeeringTriangulation("(0,1,4)(~0,3,2)(~1,5,6)", (2, 27, 20, 22, 25, 61, 34), (197, 67, 118, 79, 130, 31, 36), mutable=True)
            sage: fl.flip_back(0)
            sage: fl.flip_back(4)
            sage: fl.flip_back(2)
            sage: fl
            FlatVeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)", "BRRRRRB", (47, 27, 74, 22, 69, 61, 34), (51, 67, 16, 79, 28, 31, 36))
        """
        if check:
            if not self._mutable:
                raise ValueError("immutable flat veering triangulation; use a mutable copy instead")

            e = self._check_edge(e)
            if not self.is_backward_flippable(e):
                raise ValueError("invalid edge e={} for backward flip".format(e))

        h = 2 * e
        H = self._ep(h)
        a, b, c, d = self.square_about_half_edge(h)
        ea = a // 2
        eb = b // 2
        ec = c // 2
        ed = d // 2

        assert self._y[e] == self._y[ea] + self._y[eb] == self._y[ec] + self._y[ed]
        assert self._x[e] == abs(self._x[ea] - self._x[eb]) == abs(self._x[ec] - self._x[ed])

        if self._y[ea] > self._y[ed]:
            self._y[e] = self._y[ea] - self._y[ed]
            if col is not None:
                assert col == RED
            col = RED
        elif self._y[ea] < self._y[ed]:
            self._y[e] = self._y[ed] - self._y[ea]
            if col is not None:
                assert col == BLUE
            col = BLUE
        else:
            # equality
            self._y[e] = self._y[ea] - self._y[ed]
            if col is not None:
                assert col == PURPLE
            col = PURPLE

        self._x[e] = self._x[ea] + self._x[ed]

        self._constellation_class.flip_back(self, e, col, check=False)
        if check:
            self._check

    def _extra_relabelling(self, p):
        perm_on_edge_list(p, self._x)
        perm_on_edge_list(p, self._y)

    def xy_scaling(self, a, b):
        r"""
        Rescale the horizontal direction by `a` and the vertical one by `b`.

        EXAMPLES::

            sage: from veerer import Triangulation, FlatVeeringTriangulation
            sage: fl = FlatVeeringTriangulation("(0,1,2)(3,4,~0)(5,6,~1)", (47, 27, 74, 22, 69, 61, 34), (51, 67, 16, 79, 28, 31, 36), mutable=True)
            sage: fl.xy_scaling(2, 1/3)
            sage: fl
            FlatVeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)", "BRRRRRB", (94, 54, 148, 44, 138, 122, 68), (17, 67/3, 16/3, 79/3, 28/3, 31/3, 12))
        """
        if not self._mutable:
            raise ValueError("immutable flat veering triangulation; use a mutable copy instead")

        for i in range(self._ne):
            self._x[i] *= a
            self._y[i] *= b
