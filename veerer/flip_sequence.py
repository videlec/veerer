r"""
Dynamical forward flip sequences (and relabeling) in veering triangulations.
"""
######################################################################
# This file is part of veering.
#
#       Copyright (C) 2020 Vincent Delecroix
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

from __future__ import absolute_import

from .constants import colour_from_char, colour_to_char, RED, BLUE, PURPLE, GREEN
from .permutation import perm_init, perm_check, perm_id, perm_is_one, perm_preimage, perm_invert, perm_cycle_string, perm_compose, perm_pow, perm_conjugate
from .veering_triangulation import VeeringTriangulation
from .env import require_package, sage

def flip_sequence_to_string(sequence):
    return " ".join("%d%s" % (e, colour_to_char(col)) for e,col in sequence)

def flip_sequence_from_string(s):
    return [(int(f[:-1]), colour_from_char(f[-1])) for f in s.split()]

class VeeringFlipSequence(object):
    r"""
    A dynamical sequence of forward flips followed by a relabelling.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation, VeeringFlipSequence, BLUE, RED
        sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
        sage: F = VeeringFlipSequence(T)
        sage: F
        VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RRB"), "", "(0)(1)(2)(~2)(~1)(~0)")
        sage: F.flip(1, RED)
        sage: F.flip(0, RED)
        sage: F
        VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RRB"), "1R 0R", "(0)(1)(2)(~2)(~1)(~0)")

    The flips can also be specified in the input as a string or as a list::

        sage: VeeringFlipSequence(T, "1R 0R")
        VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RRB"), "1R 0R", "(0)(1)(2)(~2)(~1)(~0)")
        sage: VeeringFlipSequence(T, [(1, RED), (0, RED)])
        VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RRB"), "1R 0R", "(0)(1)(2)(~2)(~1)(~0)")
    """
    def __init__(self, start, sequence=None, relabelling=None, reduced=None):
        if not isinstance(start, VeeringTriangulation):
            raise TypeError("'start' must be a VeeringTriangulation")
        if reduced is None:
            reduced = any(c == PURPLE for c in start._colouring)
        if any(c == GREEN for c in start._colouring):
            raise ValueError("GREEN edges not allowed in forward flip sequences")
        elif reduced is False and any(c == PURPLE for c in start._colouring):
            raise ValueError("wrong usage of 'reduced'")

        self._start = start.copy()
        if reduced:
            self._start.forgot_forward_flippable_colour()
        self._end = self._start.copy()
        self._relabelling = perm_id(self._start._n)
        self._flips = []   # list of triples (e, col_after, col_before)

        if sequence is not None:
            if isinstance(sequence, str):
                sequence = flip_sequence_from_string(sequence)
            for e, col in sequence:
                self.flip(e, col)
        if relabelling is not None:
            self.relabel(relabelling)

    def _check(self):
        T = VeeringFlipSequence(self._start, [f[:2] for f in self._flips], self._relabelling)

        assert T._start == self._start, (T._start, self._start)
        assert T._relabelling == self._relabelling, (T._relabelling, self._relabelling)
        assert T._flips == self._flips, (T._flips, self._flips)
        assert T._end == self._end, (T._end, self._end)

    def __repr__(self):
        r"""
        TESTS::

            sage: from veerer import VeeringTriangulation, VeeringFlipSequence

            sage: T = VeeringTriangulation("(0,1,2)(~1,~2,~0)", "RRB")
            sage: VeeringFlipSequence(T, "1R 0R")
            VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RRB"), "1R 0R", "(0)(1)(2)(~2)(~1)(~0)")
            sage: VeeringFlipSequence(T, "1R 0R", reduced=True)
            VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RPB"), "1R 0R", "(0)(1)(2)(~2)(~1)(~0)")
            sage: VeeringFlipSequence(T, "1R 0R", relabelling="(0,5)(1,3)", reduced=True)
            VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RPB"), "1R 0R", "(0,~0)(1,~2)(2,~1)")
            sage: VeeringFlipSequence(T, "1R 0R", relabelling="(0,5)(1,3)", reduced=True)
            VeeringFlipSequence(VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RPB"), "1R 0R", "(0,~0)(1,~2)(2,~1)")
        """
        args = [repr(self._start)]
        args.append("\"%s\"" % flip_sequence_to_string(self.flips()))
        args.append("\"%s\"" % perm_cycle_string(self._relabelling, self._end._n, involution=self._end._ep))
        return "VeeringFlipSequence({})".format(", ".join(args))

    # properties
    def is_identical(self, other):
        if type(self) is not type(other):
            raise TypeError
        return self._start == other._start and \
               self._end == other._end and \
               self._flips == other._flips and \
               self._relabelling == other._relabelling

    def __eq__(self, other):
        # TODO: implement equality of mapping class... not of the sequence itself.
        # This is rather simple: check start, end, compute the matrices, compare.
        if type(self) is not type(other):
            raise TypeError
        return self._start == other._start and \
               self._end == other._end and \
               self._flips == other._flips and \
               self._relabelling == other._relabelling

    def __ne__(self, other):
        return not (self == other)

    def start(self, copy=True):
        if copy:
            return self._start.copy()
        else:
            return self._start

    def end(self, copy=True):
        if copy:
            return self._end.copy()
        else:
            return self._end

    def copy(self):
        F = VeeringFlipSequence.__new__(VeeringFlipSequence)
        F._start = self._start.copy()
        F._end = self._end.copy()
        F._flips = self._flips[:]
        F._relabelling = self._relabelling
        return F

    def matrix(self, twist=True):
        require_package('sage', 'matrix')
        from sage.rings.all import ZZ
        from sage.matrix.special import identity_matrix
        m = identity_matrix(ZZ, self._start.num_edges())
        V = self._start.copy()
        for e, col, _ in self._flips:
            V.flip_homological_action(e, m, twist)
            V.flip(e, col)
        V.relabel_homological_action(self._relabelling, m, twist)
        return m

    def end_colouring(self):
        r"""
        Return the colours of the end of this path as forced by the flip sequence.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringFlipSequence, BLUE, RED, PURPLE
            sage: Vc = VeeringTriangulation("(0,~5,4)(3,5,6)(1,2,~6)", "PPBPRBR")
            sage: CR5 = VeeringFlipSequence(Vc, "1B", "(1,2)")
            sage: CL5 = VeeringFlipSequence(Vc, "0R", "(0,4)")
            sage: R32 = VeeringFlipSequence(Vc, "0B 3B 5B", "(0,3)")
            sage: L32 = VeeringFlipSequence(Vc, "1R 3R 6R", "(1,3)(6,~6)")
            sage: assert R32.end() == R32.start()
            sage: assert L32.end() == L32.start()

            sage: L32.end_colouring()
            array('l', [4, 1, 2, 1, 1, 2, 1])
            sage: (L32 * CR5 * CL5).end_colouring()
            array('l', [1, 2, 2, 1, 1, 2, 1])
        """
        ne = self._end.num_edges()
        ep = self._end._ep
        colours = self._end._colouring[:ne]
        undetermined = set(i for i in range(ne) if colours[i] == PURPLE)

        # run backward through flipped edges
        i = len(self._flips) - 1
        while i >= 0 and undetermined:
            e, col, oldcol = self._flips[i]
            e = self._relabelling[e]
            if e >= ne:
                e = ep[e]
            if e in undetermined:
                undetermined.remove(e)
                colours[e] = col
            i -= 1

        # for unflipped edges, look at colours of the initial triangulation
        for e in undetermined:
            re = perm_preimage(self._relabelling, e)
            col = self._start._colouring[re]
            if col != PURPLE:
                if re >= ne:
                    re = ep[re]
                colours[e] = col

        return colours

    def coloured_start(self):
        V = self._start.copy()
        ne = V.num_edges()
        if any(V._colouring[e] == PURPLE for e in range(ne)):
            colours = self.end_colouring()
            for e in range(ne):
                if V.edge_colour(e) == PURPLE:
                    if colours[e] == PURPLE:
                        raise ValueError("undetermined colour e={}".format(e))
                    V.set_edge_colour(e, colours[e])
        return V

    def inverse(self):
        r"""
        Return a conjugate of the inverse of this mapping class as another veering flip sequence.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringFlipSequence

            sage: V = VeeringTriangulation("(0,6,5)(1,2,~6)(3,4,~5)", "BPBBRPR")
            sage: B = VeeringFlipSequence(V, "1B", "(1,2)")
            sage: R = VeeringFlipSequence(V, "1R 5R", "(0,2,3)(1,4)(5,6)")
            sage: (B * R).inverse()
            VeeringFlipSequence(VeeringTriangulation("(0,6,5)(1,2,~6)(3,4,~5)", "RBRRPBP"), "6B 4R 3B", "(0,3,1,4,2)(5,6,~5,~6)")
        """
        start = self._start
        reduced = any(start._colouring[e] == PURPLE for e in range(start.num_edges()))
        if reduced:
            # determine the coloured flip sequence
            coloured_flips = []
            V = self.coloured_start()
            for e, col, _ in self._flips:
                coloured_flips.append((e, col, V.edge_colour(e)))
                V.flip(e, col)
            V.relabel(self._relabelling)

            # TODO: remove check
            W = V.copy()
            W.forgot_forward_flippable_colour()
            assert W == self._end
        else:
            coloured_flips = self._flips
            V = self._end.copy()

        assert all(oldcol == BLUE or oldcol == RED for (_, _, oldcol) in coloured_flips)
        inverse_flips = [(self._relabelling[e], BLUE if oldcol == RED else RED) for (e, _, oldcol) in reversed(coloured_flips)]

        # NOTE: the relabelling might need some conjugation by edge flip
        # (more precisely, the edge flipped an odd number of times are
        #  flipped)
        ep = self._start._ep
        ne = self._start.num_edges()
        c = perm_id(self._start._n)
        for i,_ in inverse_flips:
            c[i], c[ep[i]] = c[ep[i]], c[i]
        r = perm_invert(self._relabelling, self._start._n)
        r = perm_compose(c, r, self._start._n)

        V.rotate()
        F = VeeringFlipSequence(V, inverse_flips, r, reduced=reduced)

        # TODO: remove this expensive check
        F._check()

        return F

    def matrix_inverse(self, twist=True):
        require_package('sage', 'matrix')
        from sage.rings.all import ZZ
        from sage.matrix.special import identity_matrix
        m = identity_matrix(ZZ, self._start.num_edges())
        V = self._start.copy()
        V.relabel_homological_action(perm_invert(self._relabelling, self._start._n), m, twist)
        for e, col, oldcol in reversed(self._flips):
            pass

    def flips(self):
        return [flip[:2] for flip in self._flips]

    def is_closed(self):
        return self._start == self._end

    def unflipped_edges(self):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringFlipSequence

        The torus::

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "PBR")
            sage: B = VeeringFlipSequence(T, "0B", "(1,0,~1,~0)(2,~2)")
            sage: R = VeeringFlipSequence(T, "0R", "(0,2)(1,~1)")
            sage: assert B.is_closed() and R.is_closed()
            sage: B.unflipped_edges()
            {2}
            sage: R.unflipped_edges()
            {1}
            sage: (B**3).unflipped_edges()
            {2}
            sage: (B * R).unflipped_edges()
            set()
            sage: (R * B).unflipped_edges()
            set()

        An example on the sphere::

            sage: Vc = VeeringTriangulation("(0,~5,4)(1,2,~6)(3,5,6)", "PPBPRBR")
            sage: Vr = VeeringTriangulation("(0,6,5)(1,2,~6)(3,4,~5)", "BPBBRPR")

            sage: CR5 = VeeringFlipSequence(Vc, "1B", "(1,2)")
            sage: CL5 = VeeringFlipSequence(Vc, "0R", "(0,4)")
            sage: R3 = VeeringFlipSequence(Vc, "0B 3B", "(0,3)")
            sage: R2 = VeeringFlipSequence(Vr, "5B")

            sage: CR5.unflipped_edges()
            {0, 3, 4, 5, 6}
            sage: CL5.unflipped_edges()
            {1, 2, 3, 5, 6}
            sage: (CL5 * CR5).unflipped_edges()
            {3, 5, 6}
            sage: (R3 * R2).unflipped_edges()
            {1, 2, 4, 6}
            sage: (R3 * R2 * CL5 * R3 * R2 * CR5 * CL5).unflipped_edges()
            {6}
        """
        if self._start != self._end:
            raise TypeError
        n = self._start.num_edges()
        ep = self._start._ep
        flipped = set(x[0] for x in self._flips)
        if len(flipped) == n:
            return set()

        new = list(flipped)
        very_new = []
        modified = True
        r = self._relabelling
        while len(flipped) < n and modified:
            modified = False
            for e in new:
                e = r[e]
                if e >= n:
                    e = ep[e]
                if e not in flipped:
                    modified = True
                    flipped.add(e)
                    very_new.append(e)
            new, very_new = very_new, new
            del very_new[:]

        E = set(range(n))
        assert flipped.issubset(E)
        E.difference_update(flipped)
        return E

    def is_pseudo_anosov(self):
        r"""
        Test whether the flip sequence defines a pseudo-Anosov mapping class.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringFlipSequence
            sage: F2 = VeeringFlipSequence(VeeringTriangulation("(0,3,4)(1,~3,5)(2,6,~4)", "PPPBRRB"), "0B 1B")
            sage: F3 = VeeringFlipSequence(VeeringTriangulation("(0,4,3)(1,5,~3)(2,6,~4)", "BBPPRRB"), "3B", "(0,1)")
            sage: F4 = VeeringFlipSequence(VeeringTriangulation("(0,4,3)(1,5,~3)(2,6,~4)", "BBPPRRB"), "2R 3R", "(0,6,1)(2,5)(3,4)")
            sage: F6 = VeeringFlipSequence(VeeringTriangulation("(0,4,3)(1,5,~3)(2,6,~4)", "BBPPRRB"), "2B", "(2,6)")

        Pseudo-Anosov examples::

            sage: assert (F2 * F4 * F3).is_pseudo_anosov()
            sage: assert (F4 * F6).is_pseudo_anosov()
            sage: assert (F4 * F4 * F6).is_pseudo_anosov()

        Non pseudo-Anosov::

            sage: assert not F2.is_pseudo_anosov()
            sage: assert not (F2 * F3).is_pseudo_anosov()
            sage: assert not (F3 * F2).is_pseudo_anosov()
            sage: assert not (F4 * F4 * F4 * F6).is_pseudo_anosov()
        """
        if self._start != self._end:
            return False
        return not self.unflipped_edges()

    def self_similar_surface(self):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation, BLUE, RED
            sage: V = VeeringTriangulation("(0,~2,1)(2,~8,~3)(3,~7,~4)(4,6,~5)(5,8,~6)(7,~1,~0)", "PRBPRBPBR")
            sage: R0, R1 = V.dehn_twists(RED)
            sage: B0, B1 = V.dehn_twists(BLUE)
            sage: f = B0*R0*B1*R1
            sage: f.self_similar_surface()
            (a,
             FlatVeeringTriangulation(Triangulation("(0,~2,1)(2,~8,~3)(3,~7,~4)(4,6,~5)(5,8,~6)(7,~1,~0)"), [(1, 1), (a^3 - 7*a^2 + 13*a - 7, -a), ..., (-a^3 + 7*a^2 - 13*a + 7, a), (-1, -1)]))

            sage: f = B1*B0*R0*B1*R1*R1*R1*R0*B1*R0*B1
            sage: f.self_similar_surface()
            (a,
             FlatVeeringTriangulation(Triangulation("(0,~2,1)(2,~8,~3)(3,~7,~4)(4,6,~5)(5,8,~6)(7,~1,~0)"), [(1, 1), ..., (-1/183*a^3 + 8/61*a^2 - 42/61*a + 274/183, 4/183*a^3 - 30/61*a^2 + 119/61*a + 8/183), (-1, -1)]))
        """
        if not self.is_pseudo_anosov():
            raise ValueError("flip sequence is not pseudo-Anosov")

        require_package('sage', 'self_similar_surface')
        from sage.rings.qqbar import AA
        hm = self.matrix() # matrix: heights_start -> heights_end
        hp = hm.charpoly()
        himax = hrmax = None
        for (fac,mult) in hp.factor():
            for (x,m) in fac.roots(AA):
                if hrmax is None or (x > 0 and x > hrmax):
                    hrmax = x
                    hmmax = mult * m
                    hfacmax = fac
        assert hrmax is not None, hroots
        r = hrmax

        # TODO: it is a bit stupid to do twice the same computation
        wm = self.inverse().matrix() # matrix: widths_end -> widths_start
        wp = wm.charpoly()
        wroots = wp.roots(AA, multiplicities=True)
        wimax = wrmax = None
        for (fac,mult) in wp.factor():
            for (x,m) in fac.roots(AA):
                if wrmax is None or (x > 0 and x > wrmax):
                    wrmax = x
                    wmmax = mult * m
                    wfacmax = fac
        assert wrmax is not None, wroots

        assert wrmax == r, (hroots, wroots)

        # NOTE: the polynomials are apparently not always equal
        # assert wp == hp, (wp, hp)

        from sage.rings.number_field.number_field import NumberField
        K = NumberField(wfacmax, 'a', embedding=wrmax)
        r = K.gen()

        h = (hm - r).right_kernel_matrix()[0]
        if h[0] < 0:
            h = -h
        w = (wm - r).right_kernel_matrix()[0]
        if w[0] < 0:
            w = -w
        assert all(x > 0 for x in w), (w, h)
        assert all(y > 0 for y in h), (w, h)

        return r, self.coloured_start()._flat_structure_from_train_track_lengths(h, w, base_ring=K)

    # change
    def flip(self, e, col):
        ep = self._end._ep
        oldcol = self._end._colouring[e]
        E = ep[e]
        if E < e:
            e = E
        self._end.flip(e, col)
        if self._relabelling[e] != e:
            # push the flip to the left of relabelling
            e = perm_preimage(self._relabelling, e)
            E = ep[e]
            if E < e:
                e = E
        self._flips.append((e, col, oldcol))

    def swap(self, e):
        r"""
        Swap the orientation of the edge ``e`` by modifying the relabelling of this flip sequence.
        """
        E = self._end._ep[e]
        self._end.swap(e)
        self._relabelling[e] = E
        self._relabelling[E] = e

        # TODO: remove check
        self._check()

    def relabel(self, r):
        end = self._end
        if not perm_check(r, end._n):
            r = perm_init(r, end._n, end._ep)
            if not perm_check(r, end._n):
                raise ValueError('invalid relabelling permutation')

        end.relabel(r)
        self._relabelling = perm_compose(self._relabelling, r)

    def __imul__(self, other):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringFlipSequence

            sage: V0 = VeeringTriangulation("(0,3,4)(1,~3,5)(2,6,~4)", "PPPBRRB")
            sage: F = VeeringFlipSequence(V0, "2B", "(2,6)")
            sage: assert F.is_closed()       
            sage: F *= F
            sage: F
            VeeringFlipSequence(VeeringTriangulation("(0,3,4)(1,~3,5)(2,6,~4)", "PPPBRRB"), "2B 6B", "(0)(1)(2)(3)(4)(5)(6)(~4)(~3)")
        """
        if type(self) != type(other):
            raise TypeError
        if self._end != other._start:
            raise ValueError("composition undefined")

        n = self._start._n
        ne = self._start.num_edges()
        r = perm_invert(self._relabelling, n)
        ep = self._start._ep
        self._flips.extend([((r[e] if r[e] < ne else ep[r[e]]), col, oldcol) for e, col, oldcol in other._flips])
        self._end = other._end.copy()
        self._relabelling = perm_compose(self._relabelling, other._relabelling)

        # TODO: remove this expensive check!!
        self._check()
        return self

    def __mul__(self, other):
        r"""
        TESTS::

            sage: from veerer import VeeringTriangulation, VeeringFlipSequence
            sage: V2 = VeeringTriangulation("(0,3,4)(1,~3,5)(2,6,~4)", "PPPBRRB")
            sage: V3 = VeeringTriangulation("(0,4,3)(1,5,~3)(2,6,~4)", "BBPPRRB")
            sage: F2 = VeeringFlipSequence(V2, "0B 1B")
            sage: F3 = VeeringFlipSequence(V3, "3B", "(0,1)")
            sage: (F2 * F3) * (F2 * F3) == (F2 * (F3 * F2)) * F3 == F2 * ((F3 * F2) * F3)
            True
        """
        res = self.copy()
        res *= other
        return res

    def __pow__(self, k):
        if self._end != self._start:
            raise ValueError("power undefined")

        k = int(k)
        if k < 0:
            raise ValueError("negative exponent")
        if k == 0:
            return VeeringFlipSequence(self._start)
        if k == 1:
            return self

        res = self.copy()
        res._relabelling = perm_pow(res._relabelling, k)

        m = len(res._flips)
        r = perm_invert(self._relabelling, self._start._n)
        ne = self._start.num_edges()
        ep = self._start._ep
        for _ in range(m * (k-1)):
            e, col, oldcol = res._flips[-m]
            res._flips.append(((r[e] if r[e] < ne else ep[r[e]]), col, oldcol))

        # TODO: remove this expensive check
        res._check()
        return res