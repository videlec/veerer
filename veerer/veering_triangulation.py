r"""
Veering triangulations of surfaces.

An edge permutation is an involution (possibly with fixed points corresponding
to folded edges). It is said to be in canonical form if it starts with cycle
representatives.
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2018 Mark Bell
#                     2018-2023 Vincent Delecroix
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
import copy
import itertools
import numbers
from random import choice, shuffle
from array import array
import ppl

from sage.sets.disjoint_set import DisjointSet
from sage.structure.element import get_coercion_model, Matrix
from sage.structure.richcmp import op_LT, op_LE, op_EQ, op_NE, op_GT, op_GE, rich_to_bool
from sage.modules.free_module import FreeModule
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ
from sage.rings.rational import Rational

from .constants import *
from .constellation import Constellation
from .permutation import *
from .misc import det2
from .triangulation import face_boundary_init, Triangulation
from .polyhedron import LinearExpressions, ConstraintSystem
from .polyhedron.linear_expression import LinearConstraint
from .polyhedron.linear_algebra import linear_form_project, vector_normalize, prime_decomposition, is_rank_one

cm = get_coercion_model()


class VeeringTriangulation(Triangulation):
    r"""
    Veering triangulation.

    A *veering triangulation* is a triangulation of a surface together with
    a colouring of the edges in red or blue so that there is no monochromatic
    face and no monochromatic vertex.

    Boundary faces (which can have any number of edges) are allowed. In which
    case, each half-edge that belong to a boundary must have a positive angle
    excess associated to it.

    EXAMPLES::

        sage: from veerer import *  # random output due to deprecation warnings from realalg

    Built from an explicit triangulation (in cycle or list form) and a list of colours::

        sage: VeeringTriangulation("(0,1,2)(~0,~1,~2)", [RED, RED, BLUE])
        VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")

    From a stratum::

        sage: from surface_dynamics import *  # optional - surface_dynamics

        sage: VeeringTriangulation.from_stratum(Stratum([2], 1))  # optional - surface_dynamics
        VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,8,~7)(~1,~8,3)(2,7,~6)(~2,~3,4)", "RRRBBBBBB")

        sage: vt = VeeringTriangulation.from_stratum(Stratum({1:4}, 2))  # optional - surface_dynamics
        sage: vt.stratum()                                                     # optional - surface_dynamics
        Q_2(1^4)

    From a flipper pseudo-Anosov map::

        sage: import flipper                # optional - flipper

        sage: T = flipper.load('S_2_1')     # optional - flipper
        sage: h = T.mapping_class('abcD')   # optional - flipper
        sage: h.is_pseudo_anosov()          # optional - flipper
        True
        sage: V = VeeringTriangulation.from_pseudo_anosov(h)  # optional - flipper
        sage: V # optional - flipper
        VeeringTriangulation("(0,~3,~1)(1,2,14)...(12,~14,~10)(~9,~4,~2)", "RBRBRRBRBBBBRBR")

    A triangulation with some purple::

        sage: VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBPBRBPRB")
        VeeringTriangulation("(0,~6,~3)(~0,2,~1)(1,7,~2)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBPBRBPRB")

    Triangulations with boundary::

        sage: VeeringTriangulation("(0,1,2)(~0,3,4)", "(~1:1)(~2:1)(~3:1)(~4:1)", "RBRBR")
        VeeringTriangulation("(0,1,2)(~0,3,4)(~1:1)(~2:1)(~3:1)(~4:1)", "RBRBR")
        sage: VeeringTriangulation("(0,1,2)(~0,3,4)(~1:1)(~2:1)(~3:1)(~4:1)", colouring="RBRBR")
        VeeringTriangulation("(0,1,2)(~0,3,4)(~1:1)(~2:1)(~3:1)(~4:1)", "RBRBR")

    Triangulations with boundary and folded edges::

        sage: VeeringTriangulation("(0,1,2)(~1:1,~2:1)", colouring="RBR")
        VeeringTriangulation("(0,1,2)(~1:1,~2:1)", "RBR")
    """
    __slots__ = ['_colouring', '_delaunay_cone']

    def __init__(self, *args, triangulation=None, boundary=None, colouring=None, mutable=False, check=True):
        if len(args) == 3:
            if triangulation is not None or boundary is not None or colouring is not None:
                raise ValueError('invalid data in constructor')
            # triangulation_data boundary colouring
            triangulation, boundary, colouring = args
        elif len(args) == 2:
            # either (triangulation, colouring)
            # or (triangulation_data, colouring)
            if triangulation is not None or colouring is not None:
                raise ValueError('invalid data in constructor')
            triangulation, colouring = args
        elif len(args) == 1:
            if triangulation is not None:
                raise ValueError('invalid data in constructor')
            triangulation, = args

        if isinstance(triangulation, Triangulation):
            fp = triangulation.face_permutation(copy=True)
            bdry = triangulation.boundary_vector(copy=True)
        else:
            if boundary is not None and isinstance(boundary, str):
                boundary_cycles, boundary = str_to_cycles_and_data(boundary)
                if isinstance(triangulation, str):
                    triangulation = str_to_cycles(triangulation)
                else:
                    triangulation = list(triangulation)
                triangulation.extend(boundary_cycles)
            fp, bdry = face_boundary_init(triangulation, boundary)

        if colouring is None:
            if isinstance(triangulation, VeeringTriangulation):
                colouring = triangulation._colouring
            else:
                raise ValueError('no colouring given')
        elif isinstance(colouring, str):
            colouring = [colour_from_char(c) for c in colouring]

        # set _colouring: half edge index --> {RED, BLUE}
        n = len(fp)
        if n % 2:
            raise ValueError("face permutation must have even length")
        ne = n // 2
        if len(colouring) != ne:
            raise ValueError("wrong colouring argument")
        colouring = array('i', colouring)

        Constellation.__init__(self, ne, None, fp, (bdry,), (colouring,), mutable, check)

    def _set_data_pointers(self):
        Triangulation._set_data_pointers(self)
        self._colouring = self._edges_data[0]

    def _check_vertex_separatrix(self, half_edge, angle):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0:1, ~2:1 , ~1:2)", "BRR")
            sage: vt._check_vertex_separatrix(1, 0)
            (1, 0)
            sage: vt._check_vertex_separatrix(2, 0)
            (2, 0)
            sage: vt._check_vertex_separatrix(1, 2)
            Traceback (most recent call last):
            ...
            ValueError: angle (=2) out of range for separatrix at half_edge=1; must be >= 0 and < 1
        """
        half_edge = self._check_half_edge(half_edge)
        if not isinstance(angle, numbers.Integral):
            raise ValueError("invalid angle for separatrix")
        angle = int(angle)
        num_seps =  self.half_edge_num_separatrices(half_edge)
        if angle < 0 or angle >= num_seps:
            raise ValueError(f"angle (={angle}) out of range for separatrix at half_edge={half_edge}; must be >= 0 and < {num_seps}")
        return (half_edge, angle)

    def _normalize_face_separatrix(self, half_edge, angle):
        if self.face_angle(half_edge) == 0:
            return (min(perm_orbit(self._fp, half_edge)), angle)

        last_angle = self.half_edge_num_separatrices(half_edge) - 1 # the valid range is between 1 and the number of separatrices
        while angle == last_angle:
            half_edge = self.previous_in_face(half_edge)
            angle = 0
            last_angle = self.half_edge_num_separatrices(half_edge) - 1
        return (half_edge, angle)

    def _check_face_separatrix(self, half_edge, angle):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0:1, ~2:1 , ~1:2)", "BRR")
            sage: vt._check_face_separatrix(1, 0)
            (3, 0)
            sage: vt._check_face_separatrix(2, 0)
            Traceback (most recent call last):
            ...
            ValueError: not a face separatrix
            sage: vt._check_face_separatrix(1, 2)
            Traceback (most recent call last):
            ...
            ValueError: angle (=2) out of range for separatrix at half_edge=1; must be >= 0 and <= 1
        """
        half_edge = self._check_half_edge(half_edge)
        if not isinstance(angle, numbers.Integral):
            raise ValueError("invalid angle for separatrix")
        angle = int(angle)
        num_seps =  self.half_edge_num_separatrices(half_edge)
        if self._bdry[half_edge] == 0:
            raise ValueError("not a face separatrix")
        if angle < 0 or angle >= num_seps:
            raise ValueError(f"angle (={angle}) out of range for separatrix at half_edge={half_edge}; must be >= 0 and <= {num_seps}")
        return self._normalize_face_separatrix(half_edge, angle)

    def _check(self, error=RuntimeError):
        """
        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: V = VeeringTriangulation("(0,1,2)", "GBR")
            Traceback (most recent call last):
            ...
            ValueError: invalid triangle (0, 1, 2) with colours (green, blue, red)
        """
        Triangulation._check(self, error)
        ne = self._ne
        n = 2 * ne
        ev = self._vp
        cols = self._colouring
        bdry = self._bdry

        if not isinstance(bdry, array) or \
           len(bdry) != n or \
            any(x < 0 for x in bdry):
            raise error('bad boundary attribute bdry={}'.format(bdry))

        if not isinstance(cols, array) or \
           len(cols) != ne or \
           any(col not in COLOURS for col in cols):
            raise error('bad colouring attribute cols={}'.format(cols))

        if bdry is not self._half_edges_data[0] or \
           cols is not self._edges_data[0]:
            raise error('wrong pointers: id(bdry)={} id(self._data[0])={} id(cols)={} id(self._data[1])={}'.format(
                id(bdry), id(self._data[0]), id(cols), id(self._data[1])))


        # faces must be of one of the following type (up to cyclic ordering)
        # non-dgenerate: BBR (BLUE), RRB (RED)
        # 1-degenerate: PBR (PURPLE), GRB (GREEN)
        # 2-degenerate: BPG (BLUE|PURPLE|GREEN), RGP (RED|GREEN|PURPLE)
        for a in range(n):
            if self._vp[a] == -1:
                continue
            if self._bdry[a]:
                continue
            col, a, b, c = self.triangle(a, check=True)
            ea = a // 2
            eb = b // 2
            ec = c // 2
            good = False
            if col == BLUE:
                good = cols[ea] == BLUE and cols[eb] == BLUE and cols[ec] == RED
            elif col == RED:
                good = cols[ea] == RED and cols[eb] == RED and cols[ec] == BLUE
            elif col == PURPLE:
                good = cols[ea] == PURPLE and cols[eb] == BLUE and cols[ec] == RED
            elif col == GREEN:
                good = cols[ea] == GREEN and cols[eb] == RED and cols[ec] == BLUE
            elif col == BLUE | PURPLE | GREEN:
                good = cols[ea] == BLUE and cols[eb] == GREEN and cols[ec] == PURPLE
            elif col == RED | PURPLE | GREEN:
                good = cols[ea] == RED and cols[eb] == PURPLE and cols[ec] == GREEN
            if not good:
               raise error('invalid triangle ({}, {}, {}) with colours ({}, {}, {})'.format(
                    self._half_edge_string(a), self._half_edge_string(b), self._half_edge_string(c),
                    colour_to_string(cols[ea]), colour_to_string(cols[eb]), colour_to_string(cols[ec])))

        # no monochromatic vertex
        for v in self.vertices():
            if bdry[v[0]]:
                continue
            col = cols[v[0] // 2]
            i = 1
            while i < len(v) and cols[v[i] // 2] == col and not bdry[v[i]]:
                i += 1
            if i == len(v):
                raise error('monochromatic vertex {} of colour {}'.format(v, colour_to_string(cols[v[0]])))

    def base_ring(self):
        return ZZ

    def non_degenerate_triangles(self, slope=VERTICAL):
        r"""
        Iterate through non-degenerate triangles.

        Triple of half-edges are ordered such that the first is always the large edge.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,3,8)(~0,5,6)(~3,4,2)(~4,1,7)", "BBBRRRRRR")
            sage: list(vt.non_degenerate_triangles())
            [(16, 0, 6), (12, 1, 10), (9, 2, 14), (8, 4, 7)]
        """
        if slope == VERTICAL:
            LAR = PURPLE
            POS = RED
            NEG = BLUE
        elif slope == HORIZONTAL:
            LAR = GREEN
            POS = BLUE
            NEG = RED

        for a, b, c in self.triangles():
            cola = self._colouring[a // 2]
            colb = self._colouring[b // 2]
            colc = self._colouring[c // 2]
            if colb == NEG and colc == POS:
                yield (a, b, c)
            elif colc == NEG and cola == POS:
                yield (b, c, a)
            elif cola == NEG and colb == POS:
                yield (c, a, b)

    def degenerate_triangles(self, slope=VERTICAL):
        r"""
        Iterate through degenerate triangles.

        Triple of half-edges are ordered such that the first is always the degenerate edge.
        """
        if slope == VERTICAL:
            ZERO = GREEN
            POS = RED
            NEG = BLUE
        elif slope == HORIZONTAL:
            ZERO = PURPLE
            POS = BLUE
            NEG = RED

        for a, b, c in self.triangles():
            cola = self._colouring[a // 2]
            colb = self._colouring[b // 2]
            colc = self._colouring[c // 2]
            if cola == ZERO:
                yield (a, b, c)
            elif colb == ZERO:
                yield (b, c, a)
            elif colc == ZERO:
                yield (c, a, b)

    def right_wedges(self, slope=VERTICAL):
        r"""
        Return the (vertical or horizontal) right sides of the wedges in this veering triangulation.

        A wedge is a pair of consecutive half edges at a vertex that jumps over a
        (vertical or horizontal) separatrix.

        INPUT:

        - ``slope`` -- either ``VERTICAL`` (default) or ``HORIZONTAL``

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VERTICAL, HORIZONTAL
            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~8,~0,~7)(~6,~1,~5)(~4,~2,~3)", "RRBRRBRRB")
            sage: vt.right_wedges(VERTICAL)
            [0, 1, 13, 7, 6, 12]
            sage: vt.right_wedges(HORIZONTAL)
            [4, 17, 11, 5, 10, 16]
        """
        return [c for a, b, c in self.non_degenerate_triangles(slope)]

    def as_linear_family(self, mutable=False):
        r"""
        Return the linear family associated to this veering triangulation.

        EXAMPLES::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", [RED, RED, BLUE])
            sage: vt.as_linear_family()
            VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])

            sage: VeeringTriangulation("(0:2,~0:4)", "R").as_linear_family()
            VeeringTriangulationLinearFamily("(0:2,~0:4)", "R", [(1)])
        """
        from .linear_family import VeeringTriangulationLinearFamily
        return VeeringTriangulationLinearFamily(self, self.generators_matrix(), mutable=mutable)

    def triangle(self, a, check=True):
        r"""
        Return a quadruple ``(colour, e0, e1, e2)`` in canonical form for the triangle with half edge ``a``.

        The canonical form concerns the order of the colour as read counter-clockwise along the
        triangle:

        - ``RED`` triangle: ``(RED, RED, BLUE)``
        - ``BLUE`` triangle: ``(BLUE, BLUE, RED)``
        - ``PURPLE`` triangle: ``(PURPLE, BLUE, RED)``
        - ``GREEN`` triangle: ``(GREEN, RED, BLUE)``
        - ``RED|PURPLE|GREEN`` triangle: ``(RED, PURPLE, GREEN)``
        - ``BLUE|GREEN|PURPLE`` triangle: ``(BLUE, GREEN, PURPLE)``

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, RED, BLUE, PURPLE, GREEN

            sage: V = VeeringTriangulation("(0,1,2)", "RRB")
            sage: assert V.triangle(0) == V.triangle(2) == V.triangle(4) == (RED, 0, 2, 4)
            sage: V = VeeringTriangulation("(0,1,2)", "BBR")
            sage: assert V.triangle(0) == V.triangle(2) == V.triangle(4) == (BLUE, 0, 2, 4)
            sage: V = VeeringTriangulation("(0,1,2)", "PBR")
            sage: assert V.triangle(0) == V.triangle(2) == V.triangle(4) == (PURPLE, 0, 2, 4)
            sage: V = VeeringTriangulation("(0,1,2)", "GRB")
            sage: assert V.triangle(0) == V.triangle(2) == V.triangle(4) == (GREEN, 0, 2, 4)
            sage: V = VeeringTriangulation("(0,1,2)", "RPG")
            sage: assert V.triangle(0) == V.triangle(2) == V.triangle(4) == (RED|PURPLE|GREEN, 0, 2, 4)
            sage: V = VeeringTriangulation("(0,1,2)", "BGP")
            sage: assert V.triangle(0) == V.triangle(2) == V.triangle(4) == (BLUE|GREEN|PURPLE, 0, 2, 4)
        """
        # non-dgenerate: BBR (BLUE), RRB (RED)
        # 1-degenerate: PBR (PURPLE), GRB (GREEN)
        # 2-degenerate: RGP (RED|GREEN|PURPLE), BPG (BLUE|GREEN|PURPLE)
        if check:
            a = self._check_half_edge(a)
            if self._bdry[a]:
                raise ValueError('boundary edge')
        b = self._fp[a]
        c = self._fp[b]
        ea = a // 2
        eb = b // 2
        ec = c // 2
        cols = self._colouring
        degenerate = PURPLE | GREEN
        standard = RED | BLUE
        ndegenerate = bool(cols[ea] & degenerate) + bool(cols[eb] & degenerate) + bool(cols[ec] & degenerate)
        if ndegenerate == 0:
            if cols[ea] == cols[eb]:
                return (cols[ea], a, b, c)
            elif cols[eb] == cols[ec]:
                return (cols[eb], b, c, a)
            elif cols[ec] == cols[ea]:
                return (cols[ec], c, a, b)
        elif ndegenerate == 1:
            if cols[ea] & degenerate:
                return (cols[ea], a, b, c)
            elif cols[eb] & degenerate:
                return (cols[eb], b, c, a)
            elif cols[ec] & degenerate:
                return (cols[ec], c, a, b)
        elif ndegenerate == 2:
            if cols[ea] & standard:
                return (cols[ea] | degenerate, a, b, c)
            elif cols[eb] & standard:
                return (cols[eb] | degenerate, b, c, a)
            elif cols[ec] & standard:
                return (cols[ec] | degenerate, c, a, b)
        return (None, None, None, None)

    @classmethod
    def from_pseudo_anosov(cls, h, mutable=False, check=True):
        r"""
        Construct the coloured triangulation of a pseudo-Anosov homeomorphism.

        EXAMPLES::

            sage: from flipper import *  # optional - flipper
            sage: from veerer import *

            sage: T = flipper.load('SB_4')  # optional - flipper
            sage: h = T.mapping_class('s_0S_1s_2S_3s_1S_2')  # optional - flipper
            sage: h.is_pseudo_anosov()  # optional - flipper
            True
            sage: VeeringTriangulation.from_pseudo_anosov(h) # optional - flipper
            VeeringTriangulation("(0,4,~1)(1,5,3)(2,~0,~3)(~5,~4,~2)", "RBBBBR")
        """
        FS = h.flat_structure()
        n = FS.triangulation.zeta

        X = {i.label: e.x for i,e in FS.edge_vectors.items()}
        Y = {i.label: e.y for i,e in FS.edge_vectors.items()}

        triangles = [[x.label for x in t] for t in FS.triangulation]
        colours = [RED if X[e]*Y[e] > 0 else BLUE for e in range(n)]
        return VeeringTriangulation(triangles, colours, mutable=mutable, check=check)

    @classmethod
    def from_square_tiled(cls, s, col=RED, mutable=False, check=True):
        r"""
        Build a veering triangulation from a square-tiled surface (or origami).

        INPUT:

        - ``s`` - a square-tiled surface

        - ``col`` - either ``RED`` or ``BLUE``

        EXAMPLES::

            sage: from surface_dynamics import Origami            # optional - surface_dynamics
            sage: from veerer import VeeringTriangulation

            sage: o = Origami('(1,2)', '(1,3)')                   # optional - surface_dynamics
            sage: T = VeeringTriangulation.from_square_tiled(o)   # optional - surface_dynamics
            sage: T                                               # optional - surface_dynamics
            VeeringTriangulation("(0,1,2)(~0,~7,~8)(~1,~5,~6)(~2,~3,~4)(3,4,5)(6,7,8)", "RRBRRBRRB")
            sage: o.stratum()                                     # optional - surface_dynamics
            H_2(2)
            sage: T.stratum()                                     # optional - surface_dynamics
            H_2(2)

        A one cylinder example in the odd component of H(4)::

            sage: o = Origami('(1,2,3,4,5)', '(1,4,3,5,2)')       # optional - surface_dynamics
            sage: T = VeeringTriangulation.from_square_tiled(o)   # optional - surface_dynamics
            sage: o.stratum()                                     # optional - surface_dynamics
            H_3(4)
            sage: T.stratum()                                     # optional - surface_dynamics
            H_3(4)
        """
        from .features import surface_dynamics_feature
        surface_dynamics_feature.require()

        from surface_dynamics.flat_surfaces.origamis.origami_dense import Origami_dense_pyx

        if col not in [BLUE, RED]:
            raise ValueError("col must be BLUE or RED")

        if not isinstance(s, Origami_dense_pyx):
            raise ValueError("input must be an origami")

        # Note: we make all edges point right and up
        # square i bottom edge = 3*i
        # square i left edge = 3*i+2
        # square i diagonal edge = 3*i+1

        faces = []
        n = s.nb_squares()  # so 3n edges in the veering triangulation
                            # (6n half edges)
        r = s.r_tuple()
        u = s.u_tuple()
        # ep used to be i <-> 6n-1-i
        fp = [None] * (6*n)
        N = 6*n - 1
        for i in range(0, n):
            # bottom triangle
            ii = 6*i
            fp[ii] = ii + 2
            fp[ii + 2] = ii + 4
            fp[ii + 4] = ii

            # top triangle
            j = 6 * r[i] + 5 # right of i = left of r[i]
            k = 6 * u[i] + 1 # top of i = bottom of u[i]
            l = ii + 3  # diagonal
            fp[j] = k
            fp[k] = l
            fp[l] = j

        colouring = [None] * (3*n)
        colouring[::3] = [RED]*n
        colouring[2::3] = [BLUE]*n
        colouring[1::3] = [col]*n

        fp = array('i', fp)
        colouring = array('i', colouring)
        boundary = array('i', [0] * (6 * n))
        return VeeringTriangulation.from_permutations(None, fp, (boundary,), (colouring,), mutable=mutable, check=check)

    @classmethod
    def from_stratum(cls, c, folded_edges=False, mutable=False, check=True):
        r"""
        Return a Veering triangulation from either a stratum, a component
        of stratum or a cylinder diagram.

        EXAMPLES::

            sage: from surface_dynamics import *   # optional - surface_dynamics
            sage: from veerer import *

            sage: T = VeeringTriangulation.from_stratum(Stratum([2], 1))    # optional - surface_dynamics
            sage: T                                                         # optional - surface_dynamics
            VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,8,~7)(~1,~8,3)(2,7,~6)(~2,~3,4)", "RRRBBBBBB")
            sage: T.stratum()                                               # optional - surface_dynamics
            H_2(2)

            sage: Q = Stratum([9,-1], 2)                                           # optional - surface_dynamics

            sage: CTreg = VeeringTriangulation.from_stratum(Q.regular_component()) # optional - surface_dynamics
            sage: CTreg.stratum()  # optional - surface_dynamics
            Q_3(9, -1)

            sage: CTirr = VeeringTriangulation.from_stratum(Q.irregular_component())  # optional - surface_dynamics
            sage: CTirr.stratum()  # optional - surface_dynamics
            Q_3(9, -1)

        Some examples built from cylinder diagram::

            sage: c = QuadraticCylinderDiagram('(0)-(0)')    # optional - surface_dynamics
            sage: VeeringTriangulation.from_stratum(c)       # optional - surface_dynamics
            VeeringTriangulation("(0,2,~1)(~0,~2,1)", "RBB")
            sage: c = QuadraticCylinderDiagram('(0,0)-(1,1,2,2,3,3)')  # optional - surface_dynamics
            sage: VeeringTriangulation.from_stratum(c)                 # optional - surface_dynamics
            VeeringTriangulation("(0,10,~9)(~0,11,~10)(1,~8,9)(~1,~7,8)(2,~6,7)(~2,~5,6)(3,~4,5)(~3,~11,4)", "RRRRBBBBBBBB")

            sage: c = CylinderDiagram('(0,6,4,5)-(3,6,5) (1,3,2)-(0,1,4,2)')  # optional - surface_dynamics
            sage: CT = VeeringTriangulation.from_stratum(c)                   # optional - surface_dynamics
            sage: CT.stratum()                                                # optional - surface_dynamics
            H_4(6)
        """
        from .features import surface_dynamics_feature
        surface_dynamics_feature.require()

        # TODO: for now there is no account of possible folded edges
        # in the cylinder diagram. This has to be changed in
        # surface_dynamics...
        if folded_edges:
            raise NotImplementedError

        from surface_dynamics.flat_surfaces.strata import Stratum, StratumComponent
        from surface_dynamics.flat_surfaces.separatrix_diagram import \
                CylinderDiagram, QuadraticCylinderDiagram

        # make sure c is converted into a cylinder diagram
        if isinstance(c, Stratum):
            if not c.is_connected():
                print('Warning: the stratum %s is not connected' % c)
            c = c.one_component().one_cylinder_diagram()
        elif isinstance(c, StratumComponent):
            c = c.one_cylinder_diagram()
        elif not (isinstance(c, CylinderDiagram) or isinstance(c, QuadraticCylinderDiagram)):
            raise ValueError("c must either be a stratum or a component of a stratum"
                     " or a cylinder diagram")

        # translate the cylinder diagram c to a triangulation
        seen = [False] * c.nseps()
        triangles = []

        m = c.nseps()  # current counter
        nfolded = 0

        for bot,top in c.cylinders():
            # len(bot) + len(top)
            l = m + len(top) - 1
            oldi = None
            for i in bot:
                assert isinstance(i,int)
                if oldi == i and folded_edges:
                    nfolded += 1
                    continue
                if seen[i]:
                    i = ~i
                else:
                    seen[i] = True
                triangles.append((i,l+1,~l))
                l += 1
                oldi = i
            l = m + len(top) - 1
            for i in top:
                assert isinstance(i,int)
                if oldi == i and folded_edges:
                    nfolded += 1
                    continue
                if seen[i]:
                    i = ~i
                else:
                    seen[i] = True
                triangles.append((i,~(l-1),l))
                l -= 1
                oldi = i
            # last one got wrong
            i, j, k = triangles.pop()
            triangles.append((i,~(k+len(bot)+len(top)-1),k))

            m += len(bot) + len(top)

        nseps = c.nseps()

        colours = [RED] * nseps + [BLUE] * (2*nseps)
        return VeeringTriangulation(triangles, colours, mutable=mutable, check=check)

    @classmethod
    def from_face_edge_perms(self, colouring, fp, ep, vp=None, boundary=None, mutable=False, check=True):
        import warnings
        warnings.warn('the method StrebelGraph.from_face_edge_perms is deprecated; use the classmethod from_permutations instead')

        n = len(fp)
        if vp is None:
            vp = array('i', [-1] * n)
            for i in range(n):
                if fp[ep(i)] != -1:
                    vp[fp[ep(i)]] = i

        if boundary is None:
            bdry = array('i', [0] * n)
        else:
            bdry = array('i', boundary)
        colouring = array('i', colouring)

        return VeeringTriangulation.from_permutations(vp, ep, fp, (bdry, colouring), mutable=mutable, check=check)

    def forgot_forward_flippable_colour(self, folded=True):
        r"""
        Make purple the colour of forward flippable edges.

        The result of this operation is entirely determined by the vertical
        train track (as only forward flippable edges have an undefined colour).

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: t = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBBBRBBRB", mutable=True)
            sage: t.forgot_forward_flippable_colour()
            sage: t
            VeeringTriangulation("(0,~6,~3)(~0,2,~1)(1,7,~2)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBPBRBPRB")
            sage: t = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBBBRBBRB", mutable=False)
            sage: t.forgot_forward_flippable_colour()
            Traceback (most recent call last):
            ...
            ValueError: immutable veering triangulation; use a mutable copy instead
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        ep = self._ep
        for e in self.forward_flippable_edges(folded=folded):
            self._colouring[e] = PURPLE

    def forgot_backward_flippable_colour(self):
        r"""
        Make green the colour of backward flippable edges.

        The result of this operation is entirely determined by the horizontal
        train track (as only forward flippable edges have an undefined colour).

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: t = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBBBRBBRB", mutable=True)
            sage: t.forgot_backward_flippable_colour()
            sage: t
            VeeringTriangulation("(0,~6,~3)(~0,2,~1)(1,7,~2)(3,5,~4)(4,8,~5)(6,~8,~7)", "RGBBRGBRB")

            sage: t = VeeringTriangulation("(0,6,~5)(1,8,~7)(2,7,~6)(3,~1,~8)(4,~2,~3)(5,~0,~4)", "RRRBBBBBB", mutable=True)
            sage: t.forgot_backward_flippable_colour()
            sage: t._check()

            sage: t = VeeringTriangulation("(0,12,~11)(1,13,~12)(2,14,~13)(3,15,~14)(4,17,~16)(5,~10,11)(6,~3,~17)(7,~2,~6)(8,~5,~7)(9,~0,~8)(10,~4,~9)(16,~15,~1)", "RRRRRRBBBBBBBBBBBB", mutable=True)
            sage: t.forgot_backward_flippable_colour()
            sage: t._check()

            sage: t = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBBBRBBRB", mutable=False)
            sage: t.forgot_backward_flippable_colour()
            Traceback (most recent call last):
            ...
            ValueError: immutable veering triangulation; use a mutable copy instead
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        ep = self._ep
        for e in self.backward_flippable_edges():
            self._colouring[e] = GREEN

    def triangulation(self, mutable=False):
        r"""
        Return the underlying triangulation.

        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], "RRB")
            sage: T.triangulation()
            Triangulation("(0,1,2)(~0,~1,~2)")
        """
        return Triangulation.copy(self, mutable, Triangulation)

    def _colouring_string(self, short=None):
        if short is not None:
            from warnings import warn
            warn("short argument in VeeringTriangulation._colouring_string is deprecated")
        n = self.num_half_edges()
        ep = self._ep
        return ''.join(colour_to_char(x) for x in self._colouring)

    def __str__(self):
        r"""
        TESTS::

            sage: from veerer import *

            sage: VeeringTriangulation("(0,1,2)", [RED, RED, BLUE])
            VeeringTriangulation("(0,1,2)", "RRB")
            sage: VeeringTriangulation("(0,1,2)(3,4,~0)", "(~4:1,~3:1,~2:1,~1:1)", "RRBRB")
            VeeringTriangulation("(0,1,2)(~0,3,4)(~1:1,~4:1,~3:1,~2:1)", "RRBRB")
            sage: t = Triangulation("(0,1,2)(3,~0,~1)", "(~3:2,~2:2)")
            sage: VeeringTriangulation(t, "RBBR")
            VeeringTriangulation("(0,1,2)(~0,~1,3)(~2:2,~3:2)", "RBBR")
        """
        cycles = perm_cycles(self._fp, n=2 * self._ne)
        face_cycles = perm_cycles_to_string([c for c in cycles if not self._bdry[c[0]]], edge_like=True)
        face_cycles += perm_cycles_to_string([c for c in cycles if self._bdry[c[0]]], edge_like=True, data=self._bdry)
        colouring = self._colouring_string()
        return "VeeringTriangulation(\"{}\", \"{}\")".format(face_cycles, colouring)

    def __repr__(self):
        return str(self)

    def half_edge_colour(self, h, check=True):
        if check:
            h = self._check_half_edge(h)
        return self._colouring[h // 2]

    def edge_colour(self, e, check=True):
        if check:
            e = self._check_edge(e)
        return self._colouring[e]

    def is_holomorphic(self):
        return not any(self._bdry)

    def is_meromorphic(self):
        return any(self._bdry)

    def is_prime(self):
        return len(self.prime_components()) == 1

    def prime_components(self):
        r"""
        Return the components of the prime_decomposition of this linear family.

        The prime decomposition is coarser than the decomposition into
        connected components. It is the finest partition so that the
        constraints is a block-diagonal matrix. The result is a partition
        of the edges as a list of lists.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily
            sage: vt = VeeringTriangulation("(0,1,3)(2,4,5)", "RRRBBB")
            sage: vt.prime_components()
            [[0, 1, 3], [2, 4, 5]]

            sage: f = VeeringTriangulationLinearFamily(vt, [[1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 1]])
            sage: f.prime_components()
            [[0, 1, 2, 3, 4, 5]]
        """
        partition = DisjointSet(self._ne)
        for comp in self.connected_components():
            for i in range(1, len(comp)):
                partition.union(comp[0], comp[i])
        return [atom for atom, _ in prime_decomposition(self.constraints_matrix(), partition)]

    def prime_decomposition(self, mutable=False, check=True):
        """
        Return the prime decomposition of this veering triangulation or family.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily
            sage: vt = VeeringTriangulation("(0,1,3)(2,4,5)", "RRRBBB")
            sage: vt.prime_decomposition()
            [([0, 1, 3],
              VeeringTriangulationLinearFamily("(0,1,2)", "RRB", [(1, 0, -1), (0, 1, 1)])),
             ([2, 4, 5],
              VeeringTriangulationLinearFamily("(0,1,2)", "RBB", [(1, 0, -1), (0, 1, 1)]))]

            sage: f = VeeringTriangulationLinearFamily(vt, [[1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 1]])
            sage: f.prime_decomposition()
            [([0, 1, 2, 3, 4, 5],
             VeeringTriangulationLinearFamily("(0,1,3)(2,4,5)", "RRRBBB", [(1, 0, 1, -1, 0, -1), (0, 1, 0, 1, 1, 1)]))]

            sage: VeeringTriangulation("(0,1,2)(~0,~1,3)(~2:1,~4:1)(~3:1,4:1)", "BRRRR").prime_decomposition()
            [([0, 1, 2, 3, 4],
             VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2:1,~4:1)(~3:1,4:1)", "BRRRR", [(1, 0, 1, 1, 0), (0, 1, 1, 1, 0), (0, 0, 0, 0, 1)]))]

        """
        from .linear_family import VeeringTriangulationLinearFamily
        ans = []
        gens = self.constraints_matrix().right_kernel_matrix()
        partition = DisjointSet(self._ne)
        for comp in self.connected_components():
            for i in range(1, len(comp)):
                partition.union(comp[0], comp[i])
        for atom, subspace in prime_decomposition(gens, partition):
            graph = self.constellation().subgraph(atom)
            ans.append((atom, VeeringTriangulationLinearFamily(graph, subspace, mutable=mutable, check=check)))
        return ans

    def half_edge_num_separatrices(self, h, slope=VERTICAL, check=True):
        h = self._check_half_edge(h)
        col0 = self._colouring[h // 2]
        col1 = self._colouring[self._vp[h] // 2]
        if slope == VERTICAL:
            return self._bdry[h] + ((col0 == RED or col0 == PURPLE) and (col1 == BLUE or col1== GREEN))
        elif slope == HORIZONTAL:
            return self._bdry[h] + ((col0 == BLUE or col0 == GREEN) and (col1 == RED or col1 == PURPLE))
        else:
            raise ValueError("invalid slope argument")

    def vertex_separatrices(self, h=None, a=None, flat=True, slope=VERTICAL):
        r"""
        Return the pairs ``(h, a)`` encoding vertex separatrices on this veering triangulation.

        INPUT:

        - ``h`` (optional half-edge) -- return only the prongs adjacent to the vertex at ``h``

        - ``flat`` (boolean, default ``False``) -- whether to return the result
          as a plain list or as a list of cycles corresponding to each vertex

        - ``slope`` -- either ``VERTICAL`` (default) or ``HORIZONTAL``

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,12,~11)(~0,~10,11)(1,16,~15)(~1,~17,6)(2,15,~14)(~2,~6,7)(3,14,~13)(~3,~7,8)(4,17,~16)(~4,~8,9)(5,13,~12)(~5,~9,10)", "RRRRRRBBBBBBBBBBBB")
            sage: vt.vertex_separatrices()
            [(0, 0),
             (9, 0),
             (10, 0),
             (1, 0),
             (2, 0),
             (5, 0),
             (6, 0),
             (11, 0),
             (3, 0),
             (4, 0),
             (7, 0),
             (8, 0)]
            sage: vt.vertex_separatrices(flat=False)
            [[(0, 0), (9, 0), (10, 0), (1, 0), (2, 0), (5, 0), (6, 0), (11, 0)],
             [(3, 0), (4, 0), (7, 0), (8, 0)]]
            sage: vt.vertex_separatrices(0)
            [(0, 0), (9, 0), (10, 0), (1, 0), (2, 0), (5, 0), (6, 0), (11, 0)]
            sage: vt.vertex_separatrices(7)
            [(7, 0), (8, 0), (3, 0), (4, 0)]

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2:1,~4:2)(~3:3,4:1)", "BRRRR")
            sage: vt.vertex_separatrices()
            [(5, 0), (8, 0), (2, 0), (7, 0), (7, 1), (7, 2), (9, 0), (9, 1), (3, 0)]
            sage: vt.vertex_separatrices(9, 1)
            [(9, 1), (3, 0), (5, 0), (8, 0), (2, 0), (7, 0), (7, 1), (7, 2), (9, 0)]
            sage: VeeringTriangulation("(0,1,2)(~0,~1,3)(~2:1,~4:2)(~3:3,4:1)", "BRRRR").vertex_separatrices(flat=False)
            [[(5, 0), (8, 0), (2, 0), (7, 0), (7, 1), (7, 2), (9, 0), (9, 1), (3, 0)]]
        """
        if slope == VERTICAL:
            right = RED
            left = BLUE
        else:
            right = BLUE
            left = RED

        if any(col == GREEN or col == PURPLE for col in self._colouring):
            raise NotImplementedError

        if h is not None:
            if a is None:
                a = 0
            orbit = [(h, b) for b in range(a, self.half_edge_num_separatrices(h, slope, check=False))]
            for hh in perm_orbit(self._vp, h)[1:]:
                orbit.extend((hh, b) for b in range(self.half_edge_num_separatrices(hh, slope, check=False)))
            orbit.extend((h, b) for b in range(a))
            return orbit if flat else [orbit]
        else:
            separatrices = []
            for cycle in self.vertices():
                orbit = []
                for h in cycle:
                    for a in range(self.half_edge_num_separatrices(h, slope, check=False)):
                        orbit.append((h, a))
                if flat:
                    separatrices.extend(orbit)
                else:
                    separatrices.append(orbit)

            return separatrices

    def face_separatrices(self, h=None, a=None, flat=True, slope=VERTICAL):
        r"""
        Return the pairs ``(h, a)`` encoding face separatrices on this veering triangulation.

        The separatrices are listed in clockwise order around the poles, so that the order
        match the identification of separatrices in prong matchings of multiscale veering
        triangulations.

        INPUT:

        - ``h`` (optional half-edge) -- if provided, only return separatrix adjacent to the face
          at ``h``

        - ``a`` (optional angle)

        - ``flat`` (boolean, default ``False``) -- whether to return the result
          as a plain list or as a list of cycles corresponding to each vertex

        - ``slope`` -- either ``VERTICAL`` (default) or ``HORIZONTAL``

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~0:1,~4:2)(~3:2,~2:3)", "RBRRB")
            sage: vt.face_separatrices()
            [(1, 0), (9, 0), (5, 0), (5, 1), (7, 0)]
            sage: seps = vt.face_separatrices(flat=False)
            sage: seps
            [[(1, 0), (9, 0)], [(5, 0), (5, 1), (7, 0)]]
            sage: vt.face_separatrices(5, 1)
            [(5, 1), (7, 0), (5, 0)]
            sage: vt.face_separatrices(5, 0)
            [(5, 0), (5, 1), (7, 0)]
            sage: all(vt.face_angle(h) == -len(sep) for sep in seps for h, a in sep)
            True

            sage: vt.face_separatrices(9)
            [(9, 0), (1, 0)]
            sage: vt.face_separatrices(7)
            [(7, 0), (5, 0), (5, 1)]

        An example in H(1^2, -1^2) where the two faces have no separatrices::

            sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:1)(~4:1)", "BRRRBBRRRB")
            sage: vt.face_separatrices(flat=True)
            []
            sage: vt.face_separatrices(flat=False)
            []
        """
        if slope == VERTICAL:
            right = RED
            left = BLUE
        else:
            right = BLUE
            left = RED

        if any(col == GREEN or col == PURPLE for col in self._colouring):
            raise NotImplementedError

        if h is not None:
            if a is None:
                a = 0
            h, a = self._check_face_separatrix(h, a)
            orbit = [(h, b) for b in range(a, self.half_edge_num_separatrices(h, slope, check=False) - 1)]
            for hh in perm_orbit(self._fp, h)[1:]:
                orbit.extend((hh, b) for b in range(self.half_edge_num_separatrices(hh, slope, check=False) - 1))
            orbit.extend((h, b) for b in range(a))
            return orbit if flat else [orbit]
        else:
            separatrices = []
            for cycle in self.boundary_faces():
                orbit = []
                for h in cycle:
                    for a in range(self.half_edge_num_separatrices(h, slope, check=False) - 1):
                        orbit.append((h, a))
                if orbit:
                    if flat:
                        separatrices.extend(orbit)
                    else:
                        separatrices.append(orbit)

            return separatrices

    def vertex_angle(self, h):
        r"""
        Return the angle at the vertex the half-edge ``h`` is adjacent to.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, RED, BLUE
            sage: T = VeeringTriangulation([(-12, 4, -4), (-11, -1, 11), (-10, 0, 10),
            ....:                            (-9, 9, 1), (-8, 8, -2), (-7, 7, 2),
            ....:                            (-6, 6, -3), (-5, 5, 3)],
            ....:   [RED, RED, RED, RED, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE])
            sage: T.vertex_angle(0)
            1
            sage: T.vertex_angle(2)
            3
        """
        h = self._check_half_edge(h)
        vp = self.vertex_permutation(copy=False)

        a = 0
        h0 = h
        col = self._colouring[h // 2]
        # NOTE: we count by multiples of pi/2 and then divide by 2
        hh = vp[h]
        while True:
            hh = vp[h]
            ccol = self._colouring[hh // 2]
            switch = bool(col != ccol and (((col & (BLUE|RED)) and (ccol & (BLUE|RED))) or (col & (GREEN|PURPLE))))
            a += switch + 2 * self._bdry[h]
            h = hh
            col = ccol
            if h == h0:
                break
        assert a % 2 == 0, a
        return a // 2

    def face_angle(self, h, check=True):
        r"""
        Return the angle associated to the pole in the middle of the face the half-edge ``h`` is adjacent to.

        EXAMPLES::

            sage: from veerer import Triangulation, VeeringTriangulation
            sage: t = Triangulation("(0,1,2)", boundary="(~2:2,~1:1,~0:1)")
            sage: vt = VeeringTriangulation(t, "BRB")
            sage: vt.face_angle(3)
            -2
        """
        if check:
            h = self._check_half_edge(h)
            if not self._bdry[h]:
                raise ValueError('h={} not on a boundary face'.format(self._half_edge_string(h)))

        fp = self.face_permutation(copy=False)

        cum_angle = 0
        alternations = 0
        num_sides = 0
        col = self._colouring[h // 2]
        h0 = h
        while True:
            hh = fp[h]
            ccol = self._colouring[hh // 2]
            cum_angle += self._bdry[h]
            alternations += (col != ccol)
            num_sides += 1
            col = ccol
            h = hh
            if h == h0:
                break
        return (num_sides - cum_angle - alternations // 2)

    def angles(self, half_edge_representatives=False):
        r"""
        Return the list of angles (divided by \pi).

        There is a positive angle for each vertex and a non-positive angle for
        each boundary face (if any).

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(-3, 1, -1), (-2, 0, 2)], [RED, BLUE, BLUE])
            sage: T.angles()
            [2]

            sage: T = VeeringTriangulation([(-6, 2, -2), (-5, 1, 5), (-4, 0, 4), (-3, 3, -1)],
            ....:                           [RED, RED, BLUE, BLUE, BLUE, BLUE])
            sage: T.angles()
            [2, 2]

            sage: T = VeeringTriangulation([(-12, 4, -4), (-11, -1, 11), (-10, 0, 10),
            ....:                            (-9, 9, 1), (-8, 8, -2), (-7, 7, 2),
            ....:                            (-6, 6, -3), (-5, 5, 3)],
            ....:   [RED, RED, RED, RED, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE])
            sage: sorted(T.angles())
            [1, 1, 1, 1, 1, 3]

        Some examples with purple edges::

            sage: t = VeeringTriangulation("(0,6,~5)(1,8,~7)(2,7,~6)(3,~1,~8)(4,~2,~3)(5,~0,~4)", "RRRBBBBBB", mutable=True)
            sage: t.forgot_forward_flippable_colour()
            sage: t.angles()
            [6]

            sage: fp = "(0,12,~11)(1,13,~12)(2,14,~13)(3,15,~14)(4,17,~16)(5,~10,11)(6,~3,~17)(7,~2,~6)(8,~5,~7)(9,~0,~8)(10,~4,~9)(16,~15,~1)"
            sage: cols = "RRRRRRBBBBBBBBBBBB"
            sage: t = VeeringTriangulation(fp, cols, mutable=True)
            sage: t.forgot_forward_flippable_colour()
            sage: t.angles()
            [3, 3, 3, 3]

        The plane with 4 marked points::

            sage: t = Triangulation("(0,1,2)(~0,3,4)", boundary="(~4:1,~3:1,~2:1,~1:1)")
            sage: VeeringTriangulation(t, "RRBRB").angles()
            [2, 2, 2, 2, -2]

        A bi-infinite cylinder with 2 marked points::

            sage: t = Triangulation("(0,1,2)(~1,~2,3)", boundary="(~0:1)(~3:1)")
            sage: VeeringTriangulation(t, "RBRR").angles()
            [2, 2, 0, 0]

        A bi-infinite cylinder with a single marked points::

            sage: t = Triangulation("", boundary="(0:1)(~0:1)")
            sage: VeeringTriangulation(t, "R").angles()
            [2, 0, 0]

        Complement of a segment in the plane::

            sage: t = Triangulation("", boundary="(0:2,~0:2)")
            sage: VeeringTriangulation(t, "R").angles()
            [2, 2, -2]

        Complement of a triangle in the plane::

            sage: t = Triangulation("(0,1,2)", boundary="(~2:2,~1:1,~0:1)")
            sage: VeeringTriangulation(t, "BRB").angles()
            [2, 2, 2, -2]
        """
        # TODO: handle non-connected stratum correctly!
        n = 2 * self._ne
        angles = []
        half_edges = []
        seen = [False] * n
        vp = self.vertex_permutation(copy=False)
        fp = self.face_permutation(copy=False)

        # zeros (and simple poles) from vertices
        for e in range(n):
            if vp[e] == -1 or seen[e]:
                continue
            a = 0
            col = self._colouring[e // 2]
            # NOTE: we count by multiples of pi/2 and then divide by 2
            half_edges.append(e)
            while not seen[e]:
                seen[e] = True
                ee = vp[e]
                ccol = self._colouring[ee // 2]
                switch = bool(col != ccol and (((col & (BLUE|RED)) and (ccol & (BLUE|RED))) or (col & (GREEN|PURPLE))))
                a += switch + 2 * self._bdry[e]
                e = ee
                col = ccol
            assert a % 2 == 0, a
            angles.append(a // 2)

        # angles at infinity from boundary faces (meromorphic differentials)
        seen = [False] * n
        for e in range(n):
            if vp[e] == -1 or seen[e] or not self._bdry[e]:
                continue

            cum_angle = 0
            alternations = 0
            num_sides = 0
            col = self._colouring[e // 2]
            half_edges.append(e)
            while not seen[e]:
                seen[e] = True
                ee = fp[e]
                ccol = self._colouring[ee // 2]
                cum_angle += self._bdry[e]
                alternations += (col != ccol)
                num_sides += 1
                col = ccol
                e = ee
            angles.append(num_sides - cum_angle - alternations // 2)
        angles.extend([1] * self.num_folded_edges())

        return (angles, half_edges) if half_edge_representatives else angles

    def is_abelian(self, certificate=False):
        r"""
        Return whether this coloured triangulation is Abelian.

        EXAMPLES:

            sage: from veerer import *

            sage: T = VeeringTriangulation([(-3, 1, -1), (-2, 0, 2)], [RED, BLUE, BLUE])
            sage: T.is_abelian()
            True

            sage: T = VeeringTriangulation([(-6, 2, -2), (-5, 1, 5), (-4, 0, 4), (-3, 3, -1)],
            ....:       [RED, RED, BLUE, BLUE, BLUE, BLUE])
            sage: T.is_abelian()
            True
            sage: T.is_abelian(certificate=True)
            (True, [True, False, True, False, False, True, False, True, False, True, False, True])
            sage: T = VeeringTriangulation([(-12, 4, -4), (-11, -1, 11), (-10, 0, 10),
            ....:      (-9, 9, 1), (-8, 8, -2), (-7, 7, 2), (-6, 6, -3), (-5, 5, 3)],
            ....:      [RED, RED, RED, RED, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE])
            sage: T.is_abelian()
            False

        Examples with purple edges::

            sage: t = VeeringTriangulation("(0,6,~5)(1,8,~7)(2,7,~6)(3,~1,~8)(4,~2,~3)(5,~0,~4)", "RRRBBBBBB", mutable=True)
            sage: t.forgot_forward_flippable_colour()
            sage: t.is_abelian()
            True

            sage: fp = "(0,12,~11)(1,13,~12)(2,14,~13)(3,15,~14)(4,17,~16)(5,~10,11)(6,~3,~17)(7,~2,~6)(8,~5,~7)(9,~0,~8)(10,~4,~9)(16,~15,~1)"
            sage: cols = "RRRRRRBBBBBBBBBBBB"
            sage: t = VeeringTriangulation(fp, cols, mutable=True)
            sage: t.forgot_forward_flippable_colour()
            sage: t.is_abelian()
            False

        Examples with green edges::

            sage: fp = "(0,6,~5)(1,8,~7)(2,7,~6)(3,~1,~8)(4,~2,~3)(5,~0,~4)"
            sage: cols = "RRRBBBBBB"
            sage: t = VeeringTriangulation(fp, cols, mutable=True)
            sage: t.forgot_backward_flippable_colour()
            sage: t.is_abelian()
            True

            sage: fp = "(0,12,~11)(1,13,~12)(2,14,~13)(3,15,~14)(4,17,~16)(5,~10,11)(6,~3,~17)(7,~2,~6)(8,~5,~7)(9,~0,~8)(10,~4,~9)(16,~15,~1)"
            sage: cols = "RRRRRRBBBBBBBBBBBB"
            sage: t = VeeringTriangulation(fp, cols, mutable=True)
            sage: t.forgot_backward_flippable_colour()
            sage: t.is_abelian()
            False

        Examples with boundaries::

            sage: t = Triangulation("", "(0:1)(~0:1)")
            sage: VeeringTriangulation(t, "R").is_abelian()
            True

            sage: t = Triangulation("", "(0:1)(1:1)(~0:1,2:1,~1:1,~2:1)")
            sage: VeeringTriangulation(t, "RRR").is_abelian()
            False

            sage: t = Triangulation("(0,1,2)(3,~0,~1)", "(~3:2,~2:1)")
            sage: VeeringTriangulation(t, "RBRR").is_abelian()
            False

            sage: t = Triangulation("(0,1,2)(3,~0,~1)", "(~3:2,~2:2)")
            sage: VeeringTriangulation(t, "RBRR").is_abelian()
            True
        """
        vp = self._vp
        cols = self._colouring

        if self.has_folded_edge():
            return (False, None) if certificate else False

        # The code attempt to give a coherent holonomy with signs for each half
        # edge. For that purpose, it is enough to store a boolean for each edge:
        #   True: (+, +) or (+,-)
        #   False: (-,-) or (-,+)
        # In other words, the half edge is stored with True if its x-coordinate
        # is positive.
        #
        # Note that RED half edge corresponds to (+,+) or (-,-) while BLUE half
        # edge corresponds to (+,-) or (-,+).
        #
        # The propagation of half-edge orientations is done by walking around
        # vertices
        oris = [None] * (2 * self._ne)  # list of orientations decided so far
        q = []

        while any(x is None for x in oris):
            h0 = 0
            while oris[h0] is not None:
                h0 += 1
            oris[h0] = True
            oris[h0 ^ 1] = False
            q = [h0, h0 ^ 1]

            while q:
                h0 = q.pop()
                h1 = vp[h0]
                o = oris[h0]
                assert o is not None
                while True:
                    # compute the orientation of f from the one of e
                    if self.half_edge_num_separatrices(h0) % 2:
                        o = not o

                    if oris[h1] is None:
                        # f is not oriented yet
                        assert oris[h1 ^ 1] is None
                        oris[h1] = o
                        oris[h1 ^ 1] = not o
                        q.append(h1 ^ 1)
                    elif oris[h1] != o:
                        # f is incoherently oriented
                        return (False, None) if certificate else False
                    else:
                        # f is correctly oriented
                        break

                    h0, h1 = h1, vp[h1]

        return (True, oris) if certificate else True

    def abelian_cover(self, mutable=False, involution_and_quotient=False):
        r"""
        Return the orientation double cover of this veering triangulation.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: V = VeeringTriangulation("(0,1,2)", "BBR")
            sage: V.abelian_cover().stratum()                   # optional - surface_dynamics
            H_1(0)
            sage: V.abelian_cover().is_connected()
            True
            sage: V.abelian_cover().abelian_cover().is_connected()
            False

            sage: V = VeeringTriangulation("(0,2,3)(1,4,~0)(5,6,~1)", "BRRBBBB")
            sage: A = V.abelian_cover()
            sage: A.stratum()                                   # optional - surface_dynamics
            H_2(2)

        The method works as expected with green and purple edges::

            sage: W = V.copy(mutable=True)
            sage: W.forgot_forward_flippable_colour()
            sage: B = A.copy(mutable=True)
            sage: B.forgot_forward_flippable_colour()
            sage: assert W.abelian_cover() == B, (W.abelian_cover(), B)

            sage: W = V.copy(mutable=True)
            sage: W.forgot_backward_flippable_colour()
            sage: B = A.copy(mutable=True)
            sage: B.forgot_backward_flippable_colour()
            sage: assert W.abelian_cover() == B, (W.abelian_cover(), B)

        And also with boundaries::

            sage: V = VeeringTriangulation("", boundary="(0:1,2:1,~0:1,~1:1)(1:1)(~2:1)", colouring="RRR")
            sage: V.stratum()  # optional - surface_dynamics
            Q_0(1^2, -2^3)
            sage: V.abelian_cover().stratum()  # optional - surface_dynamics
            H_0(2^2, -1^6)
        """
        # As in the method is_abelian we propagate the orientation of half-edges around
        # vertices and (possibly folded) edges. We use the following conventions in
        # the covering
        # {0, ..., n-1} : half-edges positively oriented
        # {n, ..., 2n-1} : half-edges negatively oriented
        vp = self._vp
        cols = self._colouring

        n = (4 * self._ne - 2 * self.num_folded_edges())

        j = 2 * self._ne
        inv = array('i', [-1] * n)  # involution on the cover
        quot = array('i', [-1] * n)  # quotient map
        bdry_cov = array('i', [-1] * n)
        cols_cov = array('i', [-1] * (n // 2))
        for e in range(self._ne):
            quot[2 * e] = 2 * e
            if self._vp[2 * e + 1] == -1:
                inv[2 * e] = 2 * e + 1
                bdry_cov[2 * e] = bdry_cov[2 * e + 1] = self._bdry[2 * e]
                cols_cov[e] = cols[e]
                quot[2 * e + 1] = 2 * e
            else:
                bdry_cov[2 * e] = bdry_cov[j + 1] = self._bdry[2 * e]
                bdry_cov[2 * e + 1] = bdry_cov[j] = self._bdry[2 * e + 1]
                inv[2 * e] = j + 1
                inv[2 * e + 1] = j
                cols_cov[e] = cols_cov[j // 2] = cols[e]
                quot[2 * e + 1] = 2 * e + 1
                quot[j] = 2 * e + 1
                quot[j + 1] = 2 * e
                j += 2

        vp_cov = array('i', [-1] * n)
        for e in range(2 * self._ne):
            f = vp[e]
            if f == -1:
                continue
            if (((cols[e // 2] == RED or cols[e // 2] == PURPLE) and (cols[f // 2] == BLUE or cols[f // 2] == GREEN)) + self._bdry[e] + (e % 2 != f % 2)) % 2:
                vp_cov[e] = inv[f]
                vp_cov[inv[e]] = f
            else:
                vp_cov[e] = f
                vp_cov[inv[e]] = inv[f]

        vt_cov = VeeringTriangulation.from_permutations(vp_cov, None, (bdry_cov,), (cols_cov,), mutable=mutable, check=True)
        return (vt_cov, inv, quot) if involution_and_quotient else vt_cov

    def stratum(self):
        r"""
        Return the Abelian or quadratic stratum of this coloured triangulation.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: T.stratum()  # optional - surface_dynamics
            H_1(0)

            sage: fp = '(0,1,2)(~0,~3,~8)(3,5,4)(~4,~1,~5)(6,7,8)(~6,9,~2)'
            sage: cols = 'BRBRBBBRBR'
            sage: T = VeeringTriangulation(fp, cols)
            sage: T.stratum()  # optional - surface_dynamics
            Q_1(1^2, -1^2)

        Some examples with purple edges::

            sage: from surface_dynamics import Stratum                    # optional - surface_dynamics
            sage: C = Stratum([2], 1)                                     # optional - surface_dynamics
            sage: t = VeeringTriangulation.from_stratum(C, mutable=True)  # optional - surface_dynamics
            sage: t.forgot_forward_flippable_colour()                     # optional - surface_dynamics
            sage: t.stratum()                                             # optional - surface_dynamics
            H_2(2)

            sage: C = Stratum([1,1,1,1], 2)                                      # optional - surface_dynamics
            sage: t = VeeringTriangulation.from_stratum(C, mutable=True)         # optional - surface_dynamics
            sage: t.forgot_forward_flippable_colour()                            # optional - surface_dynamics
            sage: t.stratum()                                                    # optional - surface_dynamics
            Q_2(1^4)

        Some examples with boundaries::

            sage: t = Triangulation("", "(0:1)(~0:1)")
            sage: VeeringTriangulation(t, "R").stratum()  # optional - surface_dynamics
            H_0(0, -1^2)

            sage: t = Triangulation("(0,1,2)(3,~0,~1)", "(~3:2,~2:2)")
            sage: VeeringTriangulation(t, "RBRR").stratum()  # optional - surface_dynamics
            H_1(2, -2)

        A non-connected example::

            sage: vt = VeeringTriangulation("(0,~6,~5)(1,2,~7)(3,~0,6)(7,~1,~4)", boundary="(4:2,~2:2)(5:2,~3:2)", colouring="RBRRRRBR")
            sage: vt.stratum()  # optional - surface_dynamics
            (H_1(2, -2), H_1(2, -2))
        """
        if not self.is_connected():
            return tuple(component.stratum() for component in self.connected_components_subgraphs())

        from .features import surface_dynamics_feature
        surface_dynamics_feature.require()
        from surface_dynamics import Stratum

        from surface_dynamics.flat_surfaces.strata import Stratum

        A = self.angles()
        if any(a % 2 for a in A) or not self.is_abelian():
            return Stratum([(a - 2) for a in A], 2)
        else:
            return Stratum([(a - 2) // 2 for a in A], 1)

    def dimension(self):
        r"""
        Return the dimension of the ambient stratum of Abelian or quadratic differential.

        EXAMPLES::

            sage: from veerer import *
            sage: t0 = Triangulation("(0,1,2)(~0,3,~2)", boundary="(~3:1)(~1:1)")
            sage: t1 = Triangulation("(0,1,2)(~0,3,~2)", boundary="(~3:1,~1:1)")
            sage: vt = VeeringTriangulation(t0, "BBRB")
            sage: assert vt.dimension() == vt.as_linear_family().dimension() == 2
            sage: assert vt.stratum().dimension() == 2  # optional - surface_dynamics # not tested (not yet in surface_dynamics)

        An example in H(2,-2)::

            sage: fp = "(0,2,1)(~0,3,~1)"
            sage: bdry = "(~2:2,~3:2)"
            sage: cols = "BRRR"
            sage: vt = VeeringTriangulation(fp, bdry, cols)
            sage: assert vt.dimension() == vt.as_linear_family().dimension() == 2
            sage: assert vt.stratum().dimension() == 2  # optional - surface_dynamics # not tested (not yet in surface_dynamics)

        An example in Q(-1^2, -2)::

            sage: vt = VeeringTriangulation("(0:1)", "B")
            sage: vt.dimension()
            1
            sage: vt.stratum().dimension()  # optional - surface_dynamics # not tested (not yet in surface_dynamics)
            1

        An example with a disconnected linear family::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily, DelaunayStrebelAutomaton
            sage: vt = VeeringTriangulation("(1,3,~2)(2,6,~3)(4,~6,~5)(7,~11,~8)(8,9,10)(11,~20,~12)(13,~17,~14)(14,15,16)(17,~19,~18)(19,~15,~16)(20,~9,~10)(~4,~1,~0)", boundary="(0:1)(5:1)(12:1,~13:1)(18:1,~7:1)", colouring="RRRBBRRRRBRBRRRBRBRRR")
            sage: subspace = [(2, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0),
            ....:           (0, 2, 0, 2, -2, 0, 2, 0, 1, 1, 0, -1, 0, 0, 1, 1, 0, -1, 0, 1, 1),
            ....:                     (0, 0, 2, -2, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0)]
            sage: f = VeeringTriangulationLinearFamily(vt, subspace)
            sage: f.stratum_dimension()
            9
        """
        # each folded edge gives a simple pole
        ans = self.num_boundary_faces() + self.num_vertices() + self.num_folded_edges()
        if self.is_connected():
            ans += 2 * self.genus() - 2 + (self.is_holomorphic() and self.is_abelian())
        else:
            for comp in self.connected_components():
                # NOTE: the code below could be called by a VeeringTriangulationLinearFamily
                # for which the subgraph code is broken
                # see https://github.com/flatsurf/veerer/issues/54
                G = VeeringTriangulation.subgraph(self.constellation(), comp)
                ans += 2 * G.genus() - 2 + (G.is_holomorphic() and G.is_abelian())
        return ans

    stratum_dimension = dimension

    def colours_about_half_edge(self, h, check=True):
        r"""
        Return the list of colours of the quadrilateral around the half-edge ``h``.
        """
        if check:
            h = self._check_half_edge(h)
        return [self._colouring[f // 2] for f in self.square_about_half_edge(h, check=False)]

    def alternating_square(self, e, check=True):
        r"""
        Return whether there is an alternating square around the edge ``e``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: V = VeeringTriangulation([(0,1,2), (-1,-2,-3)], "RRB")
            sage: V.alternating_square(0)
            True
            sage: V.alternating_square(1)
            True
            sage: V.alternating_square(2)
            False
        """
        if check:
            e = self._check_edge(e)
        h = 2 * e
        colours = self.colours_about_half_edge(h, check=False)
        if any(colours[f] == GREEN or colours[f] == PURPLE for f in range(4)):
            return False
        return all(colours[f] != colours[(f+1) % 4] for f in range(4))

    # TODO: change the names
    # TODO: compute it combinatorially, not via polytope computation
    # (these are the cycles and, if not orientable, the dumbbells)
    def vertex_cycles(self, slope=VERTICAL, backend=None):
        r"""
        Return the rays of the train-track polytope.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, HORIZONTAL, VERTICAL
            sage: V = VeeringTriangulation([(0,1,2), (-1,-2,-3)], "RRB")
            sage: sorted(V.vertex_cycles())
            [[0, 1, 1], [1, 1, 0]]
            sage: sorted(V.vertex_cycles(HORIZONTAL))
            [[1, 0, 1], [1, 1, 0]]
        """
        return self.cone(slope, backend=backend).rays()

    def branches(self, slope=VERTICAL):
        r"""
        Return a 3-tuple made of the lists of respectively the small, mixed
        and large edges of the underlying train track.

        INPUT:

        - ``slope`` (optional) - either ``HORIZONTAL`` or ``VERTICAL``

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, HORIZONTAL
            sage: vt = VeeringTriangulation("(0,~3,2)(1,5,~2)(3,9,~4)(4,~11,~5)(6,10,~7)(7,11,~8)(8,~10,~9)(~6,~1,~0)", "RBBBBRBRBRBB")
            sage: vt.branches()
            ([0, 1, 5, 7, 9, 10], [2, 3, 8, 11], [4, 6])
            sage: vt.branches(HORIZONTAL)
            ([0, 4, 5, 6, 7, 9], [2, 3, 8, 11], [1, 10])
        """
        n = self.num_half_edges()
        ne = self.num_edges()
        fp = self.face_permutation(copy=False)
        w = [0] * ne
        seen = [False] * n
        if slope == VERTICAL:
            left = BLUE
            right = RED
        elif slope == HORIZONTAL:
            left = RED
            right = BLUE
        else:
            raise ValueError('slope must be HORIZONTAL or VERTICAL')
        for e in range(n):
            if seen[e]:
                continue

            # go to the right transition
            a = e
            while self.half_edge_colour(a) != left or self.half_edge_colour(fp[a]) != right:
                a = fp[a]
            b = fp[a]
            c = fp[b]
            w[c // 2] += 1  # half large
            seen[a] = seen[b] = seen[c] = True

        small = []
        mixed = []
        large = []
        for e in range(ne):
            if fp[2 * e + 1] == -1:  # folded edge
                w[e] *= 2
            if w[e] == 0:
                small.append(e)
            elif w[e] == 1:
                mixed.append(e)
            elif w[e] == 2:
                large.append(e)
            else:
                raise RuntimeError

        return (small, mixed, large)

    def is_flippable(self, e, check=True):
        r"""
        Return whether the edge ``e`` can be flipped.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: T.is_flippable(0)
            True
            sage: T.is_flippable(1)
            True
            sage: T.is_flippable(2)
            False
        """
        if check:
            e = self._check_edge(e)
        return Triangulation.is_flippable(self, e, check=False) and self.alternating_square(e, check=False)

    def is_forward_flippable(self, e, check=True):
        r"""
        Return whether one can perform a forward flip to the edge ``e``.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: [T.is_forward_flippable(e) for e in range(3)]
            [False, True, False]

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [GREEN, RED, BLUE])
            sage: [T.is_forward_flippable(e) for e in range(3)]
            [False, True, True]

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [PURPLE, BLUE, RED])
            sage: [T.is_forward_flippable(e) for e in range(3)]
            [True, False, False]

            sage: faces = "(0,4,3)(1,~3,5)(2,6,~4)"
            sage: x = (2, 6, 3, 4, 2, 2, 1)
            sage: y = (10, 2, 3, 4, 6, 2, 3)
            sage: cols = "BBRBRRB"
            sage: fl = FlatVeeringTriangulation(faces, cols, x, y)
            sage: fl.is_forward_flippable(1)
            True
            sage: fl.is_forward_flippable(3)
            False
        """
        if check:
            e = self._check_edge(e)
        if self._colouring[e] == GREEN or not Triangulation.is_flippable(self, e, check=False):
            return False
        if self._colouring[e] == PURPLE:
            return True
        ca, cb, cc, cd = self.colours_about_half_edge(2 * e, check=False)
        return bool(ca & (BLUE | GREEN)) and bool(cb & (RED | GREEN)) and bool(cc & (BLUE | GREEN)) and bool(cd & (RED | GREEN))

    def is_backward_flippable(self, e, check=True):
        r"""
        Return whether one can perform a backward flip to the edge ``e``.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: [T.is_backward_flippable(e) for e in range(3)]
            [True, False, False]

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [GREEN, RED, BLUE])
            sage: [T.is_backward_flippable(e) for e in range(3)]
            [True, False, False]

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [PURPLE, BLUE, RED])
            sage: [T.is_backward_flippable(e) for e in range(3)]
            [False, True, True]
        """
        if check:
            e = self._check_edge(e)
        if self._colouring[e] == PURPLE or not Triangulation.is_flippable(self, e, check=False):
            return False
        if self._colouring[e] == GREEN:
            return True
        ca, cb, cc, cd = self.colours_about_half_edge(2 * e, check=False)
        return bool(ca & (RED | PURPLE)) and bool(cb & (BLUE | PURPLE)) and bool(cc & (RED | PURPLE)) and bool(cd & (BLUE | PURPLE))

    def forward_flippable_edges(self, folded=True):
        r"""
        Return the set of forward flippable edges.

        INPUT:

        - ``folded`` - boolean (default ``True``) - whether to include folded edges

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: T.forward_flippable_edges()
            [1]

            sage: T = VeeringTriangulation("(0,1,2)", [RED, RED, BLUE])
            sage: T.forward_flippable_edges()
            [1]

        Examples with boundaries in the stratum H_1(2, -2)::

            sage: t = Triangulation("(0,2,1)(3,~1,~0)", boundary="(~3:2,~2:2)")
            sage: vtB0 = VeeringTriangulation(t, "RRBB")
            sage: vtB1 = VeeringTriangulation(t, "RBBB")
            sage: vtB2 = VeeringTriangulation(t, "BRBB")
            sage: vtR0 = VeeringTriangulation(t, "BBRR")
            sage: vtR1 = VeeringTriangulation(t, "BRRR")
            sage: vtR2 = VeeringTriangulation(t, "RBRR")

            sage: vtB0.forward_flippable_edges()
            [0]
            sage: vtB1.forward_flippable_edges()
            []
            sage: vtB2.forward_flippable_edges()
            [0]

            sage: vtR0.forward_flippable_edges()
            [1]
            sage: vtR1.forward_flippable_edges()
            [1]
            sage: vtR2.forward_flippable_edges()
            []

        TESTS::

            sage: from veerer.permutation import perm_random_centralizer
            sage: from veerer.veering_triangulation import VeeringTriangulation
            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], "RRB", mutable=True)
            sage: for _ in range(10):
            ....:     rel = perm_random_centralizer(T.edge_permutation())
            ....:     T.relabel(rel)
            ....:     assert len(T.forward_flippable_edges()) == 1
        """
        vp = self._vp
        if folded:
            return [e for e in range(self._ne) if self.is_forward_flippable(e, check=False)]
        return [e for e in range(self._ne) if vp[2 * e + 1] != -1 and self.is_forward_flippable(e, check=False)]

    def backward_flippable_edges(self, folded=True):
        r"""
        Return the list of backward flippable edges.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: T.backward_flippable_edges()
            [0]

            sage: T = VeeringTriangulation("(0,1,2)", [RED, RED, BLUE])
            sage: T.backward_flippable_edges()
            [0]

        Examples with boundaries in the stratum H_1(2, -2)::

            sage: t = Triangulation("(0,2,1)(3,~1,~0)", boundary="(~3:2,~2:2)")
            sage: vtB0 = VeeringTriangulation(t, "RRBB")
            sage: vtB1 = VeeringTriangulation(t, "RBBB")
            sage: vtB2 = VeeringTriangulation(t, "BRBB")
            sage: vtR0 = VeeringTriangulation(t, "BBRR")
            sage: vtR1 = VeeringTriangulation(t, "BRRR")
            sage: vtR2 = VeeringTriangulation(t, "RBRR")

            sage: vtB0.backward_flippable_edges()
            [1]
            sage: vtB1.backward_flippable_edges()
            [1]
            sage: vtB2.backward_flippable_edges()
            []

            sage: vtR0.backward_flippable_edges()
            [0]
            sage: vtR1.backward_flippable_edges()
            []
            sage: vtR2.backward_flippable_edges()
            [0]
        """
        vp = self._vp
        if folded:
            return [e for e in range(self._ne) if self.is_backward_flippable(e, check=False)]
        return [e for e in range(self._ne) if vp[2 * e + 1] != -1 and self.is_backward_flippable(e, check=False)]

    def purple_edges(self, folded=True):
        r"""
        Return the list of edges coloured purple.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: t = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBPBRBPRB")
            sage: t.purple_edges()
            [2, 6]
        """
        vp = self._ep
        colouring = self._colouring
        ne = self._ne
        if folded:
            return [e for e in range(ne) if colouring[e] == PURPLE]
        return [e for e in range(ne) if vp[2 * e + 1] != -1 and self._colouring[e] == PURPLE]

    def mostly_sloped_edges(self, slope):
        if slope == HORIZONTAL:
            return self.forward_flippable_edges()
        elif slope == VERTICAL:
            return self.backward_flippable_edges()
        else:
            raise ValueError

        Triangulation.relabel(self, p, check=False)
        perm_on_list(p, self._colouring)

    def set_edge_colour(self, e, col, check=True):
        r"""
        Set the colour of the edge ``e`` to ``col``.
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        if check:
            e = self._check_edge(e)
            if self._colouring[e] != PURPLE and self._colouring[e] != GREEN:
                raise ValueError("only PURPLE and GREEN edges could be changed colours")
            if col != BLUE and col != RED:
                raise ValueError("the new colour 'col' must be RED or BLUE")

        self._colouring[e] = col

    def set_random_colours(self):
        r"""
        Set random colours to the GREEN and PURPLE edges.
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        ep = self._ep
        recolour = []
        cols = [BLUE, RED]
        for e, col in enumerate(self._colouring):
            if col == GREEN or col == PURPLE:
                E = ep[e]
                shuffle(cols)
                oldcol = self._colouring[e]
                self._colouring[e] = self._colouring[E] = cols[0]
                if not self.edge_has_curve(e):
                    self._colouring[e] = self._colouring[E] = cols[1]
                    assert self.edge_has_curve(e)
                recolour.append((e, oldcol))
                if e != E:
                    recolour.append((E, oldcol))

    def set_colour(self, col):
        r"""
        Set all GREEN or PURPLE edges to ``col``.

        The colour ``col`` must be RED or BLUE.
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        if col != RED and col != BLUE:
            raise ValueError("'col' must be RED or BLUE")

        for e in range(self._ne):
            if self._colouring[e] == GREEN or self._colouring[e] == PURPLE:
                self._colouring[e] = col

    def rotate(self):
        r"""
        Apply the pi/2 rotation.

        This amount to change the colouring (the combinatorics of the
        triangulation remains unchanged).

        EXAMPLES::

            sage: from veerer import *

            sage: faces = "(0,1,2)(~0,~4,~2)(3,4,5)(~3,~1,~5)"
            sage: cols = [BLUE,RED,RED,BLUE,RED,RED]
            sage: T = VeeringTriangulation(faces, cols, mutable=True)
            sage: T.rotate()
            sage: T
            VeeringTriangulation("(0,1,2)(~0,~4,~2)(~1,~5,~3)(3,4,5)", "RBBRBB")
            sage: T._check()

            sage: fp = "(0,12,~11)(1,13,~12)(2,14,~13)(3,15,~14)(4,17,~16)(5,~10,11)(6,~3,~17)(7,~2,~6)(8,~5,~7)(9,~0,~8)(10,~4,~9)(16,~15,~1)"
            sage: cols = "RRRRRRBBBBBBBBBBBB"
            sage: T0 = VeeringTriangulation(fp, cols)
            sage: T = T0.copy(mutable=True)
            sage: T.rotate()
            sage: T.conjugate()
            sage: S = T0.copy(mutable=True)
            sage: S.conjugate()
            sage: S.rotate()
            sage: S == T
            True

        Check that PURPLE edges are mapped to GREEN::

            sage: T = VeeringTriangulation("(0,1,2)(3,4,5)(~5,~3,~1)(~4,~2,~0)", "BRPBRP", mutable=True)
            sage: T.rotate()
            sage: T
            VeeringTriangulation("(0,1,2)(~0,~4,~2)(~1,~5,~3)(3,4,5)", "RBGRBG")
            sage: T.rotate()
            sage: T
            VeeringTriangulation("(0,1,2)(~0,~4,~2)(~1,~5,~3)(3,4,5)", "BRPBRP")

        Forward and backward delaunay flips are interchanged under a rotation::

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRBBBR", mutable=True)
            sage: vt.delaunay_cone()
            8-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRBBBR") made of
             2 forward-flip facets
             2 backward-flip facets
             5 x-degeneration facets
             4 y-degeneration facets
            sage: sorted(vt.delaunay_flips())
            [([1], 1), ([1], 2), ([5, 6], 1), ([5, 6], 2)]
            sage: sorted(vt.backward_delaunay_flips())
            [([0], 1), ([0], 2), ([7], 1), ([7], 2)]
            sage: vt.rotate()
            sage: vt.delaunay_cone()
            8-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BBRRBRRRB") made of
             2 forward-flip facets
             2 backward-flip facets
             4 x-degeneration facets
             5 y-degeneration facets
            sage: sorted(vt.delaunay_flips())
            [([0], 1), ([0], 2), ([7], 1), ([7], 2)]
            sage: sorted(vt.backward_delaunay_flips())
            [([1], 1), ([1], 2), ([5, 6], 1), ([5, 6], 2)]
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')
        for i, col in enumerate(self._colouring):
            if col == RED:
                self._colouring[i] = BLUE
            elif col == BLUE:
                self._colouring[i] = RED
            elif col == PURPLE:
                self._colouring[i] = GREEN
            else:
                assert col == GREEN
                self._colouring[i] = PURPLE

    def conjugate(self):
        r"""
        Conjugate this triangulation.

        EXAMPLES::

            sage: from veerer import *

            sage: faces = "(0,1,2)(~0,~4,~2)(3,4,5)(~3,~1,~5)"
            sage: cols = [BLUE,RED,RED,BLUE,RED,RED]
            sage: T = VeeringTriangulation(faces, cols, mutable=True)
            sage: T.conjugate()
            sage: T
            VeeringTriangulation("(0,2,4)(~0,~2,~1)(1,3,5)(~3,~5,~4)", "RBBRBB")
            sage: T._check()

            sage: T = VeeringTriangulation(faces, cols, mutable=False)
            sage: T.conjugate()
            Traceback (most recent call last):
            ...
            ValueError: immutable veering triangulation; use a mutable copy instead
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        Triangulation.conjugate(self)
        transp = {RED: BLUE, BLUE: RED, GREEN: GREEN, PURPLE: PURPLE}
        for i in range(self._ne):
            self._colouring[i] = transp[self._colouring[i]]

    def flip(self, e, col, Lx=None, Gx=None, reduced=None, check=True):
        r"""
        Flip an edge inplace.

        INPUT:

        - ``e`` - edge number

        - ``col`` - colour of the edge after the flip (ie either ``RED``, ``BLUE`` or ``GREEN``)

        - ``Lx`` - (optional) - matrix whose rows are equations in a linear subspace
          that has to be carried around

        - ``Gx`` - (optional) - matrix whose rows are generators of a linear subspace
          that has to be carried around

        - ``reduced`` -- whether to change the colours of the neighbors edges to ``PURPLE``
          if they become forward flippable.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", mutable=True)
            sage: T.flip(1, RED)
            sage: T
            VeeringTriangulation("(0,~2,1)(~0,2,~1)", "RRB")
            sage: T.flip(0, RED)
            sage: T
            VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: T.flip(1, BLUE)
            sage: T
            VeeringTriangulation("(0,~2,1)(~0,2,~1)", "RBB")
            sage: T.flip(2, BLUE)
            sage: T
            VeeringTriangulation("(0,~1,~2)(~0,1,2)", "RBB")

        The same flip sequence with reduced veering triangulations (forward flippable
        edges in ``PURPLE``)::

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", mutable=True)
            sage: T.forgot_forward_flippable_colour()
            sage: T
            VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RPB")
            sage: T.flip(1, RED)
            sage: T
            VeeringTriangulation("(0,~2,1)(~0,2,~1)", "PRB")
            sage: T.flip(0, RED)
            sage: T
            VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RPB")
            sage: T.flip(1, BLUE)
            sage: T
            VeeringTriangulation("(0,~2,1)(~0,2,~1)", "RBP")
            sage: T.flip(2, BLUE)
            sage: T
            VeeringTriangulation("(0,~1,~2)(~0,1,2)", "RPB")

        Some examples involving linear subspaces::

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: T = T.copy(mutable=True)
            sage: Gx = matrix(ZZ, [s, t])
            sage: T.flip(3, 2, Gx=Gx)
            sage: T.flip(4, 2, Gx=Gx)
            sage: T.flip(5, 2, Gx=Gx)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(0), VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(1), VERTICAL)

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(2, 3, 4, 5, 1, 2)
            sage: T = T.copy(mutable=True)
            sage: Gx = matrix(ZZ, [s, t])
            sage: flip_sequence = [(3, 2), (4, 1), (5, 2), (6 , 2), (5, 1), (1, 1), (5, 1)]
            sage: for e, col in flip_sequence:
            ....:     T.flip(e, col, Gx=Gx)
            ....:     T._set_subspace_constraints(T._constraint_check, Gx.row(0), VERTICAL)
            ....:     T._set_subspace_constraints(T._constraint_check, Gx.row(1), VERTICAL)
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        if check:
            if col != BLUE and col != RED and col != GREEN:
                raise ValueError("'col' must be BLUE, RED or GREEN")

            e = self._check_edge(e)
            if not self.is_forward_flippable(e, check=False):
                raise ValueError("half-edge e={} is not forward flippable".format(e))

        h = 2 * e

        if reduced is None:
            reduced = self._colouring[e] == PURPLE

        if Lx is not None:
            raise NotImplementedError("not implemented for linear equations")
        if Gx is not None:
            a, b, c, d = self.square_about_half_edge(h, check=False)
            ea = a // 2
            ed = d // 2

            eb = b // 2
            ec = c // 2
            assert Gx.column(e) == Gx.column(ea) + Gx.column(eb) == Gx.column(ec) + Gx.column(ed)
            if col == RED:
                # ve <- vd - va
                # e-th column becomes d-th column minus a-th column
                Gx.add_multiple_of_column(e, e, -1)
                Gx.add_multiple_of_column(e, ed, +1)
                Gx.add_multiple_of_column(e, ea, -1)
            elif col == BLUE:
                # ve <- va - vd
                Gx.add_multiple_of_column(e, e, -1)
                Gx.add_multiple_of_column(e, ed, -1)
                Gx.add_multiple_of_column(e, ea, +1)
            else:
                raise NotImplementedError('GREEN not implemented with linear subspace')

        # flip and set colour
        ep = self._ep
        Triangulation.flip(self, e, check=False)
        self._colouring[e] = col

        if reduced:
            a, b, c, d = self.square_about_half_edge(h, check=False)
            assert self._colouring[a // 2] & (RED | GREEN)
            assert self._colouring[b // 2] & (BLUE | GREEN)
            assert self._colouring[c // 2] & (RED | GREEN)
            assert self._colouring[d // 2] & (BLUE | GREEN)
            assert not self.is_forward_flippable(e)

            if col == BLUE:
                if self.is_forward_flippable(b // 2, check=False):
                    self._colouring[b // 2] = PURPLE
                if d != ep(b) and self.is_forward_flippable(d // 2, check=False):
                    self._colouring[d // 2] = PURPLE
                assert not self.is_forward_flippable(a // 2)
                assert not self.is_forward_flippable(c // 2)
            elif col == RED:
                if self.is_forward_flippable(a // 2, check=False):
                    self._colouring[a // 2] = PURPLE
                if c != ep(a) and self.is_forward_flippable(c // 2, check=False):
                    self._colouring[c // 2] = PURPLE
                assert not self.is_forward_flippable(b // 2)
                assert not self.is_forward_flippable(d // 2)
            else:
                assert col == GREEN
                # should we put all edges in a cylinder PURPLE?

    def cylinders(self, col):
        r"""
        Return the list of cylinders of colour ``col``.

        Each cylinder is given as a quadruple ``(middle, rbdry, lbdry, pocket)`` where

        - ``middle`` are the half-edges crossed by the core curve of the annulus

        - ``rbdry`` and ``lbdry`` are either two lists of half-edge boundaries or,
          in the case of "pocket cylinder" the list of half-edge boundaries cut by
          the folded edges.

        - ``pocket`` (boolean) whether this is a pocket cylinder

        In the case of "pocket cylinder", the first and last elements of
        ``middle`` are the folded edges.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, RED, BLUE

        The torus::

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: T.cylinders(RED)
            [([0, 3], [4], [5], False)]
            sage: T.cylinders(BLUE)
            []

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "BRB")
            sage: T.cylinders(BLUE)
            [([4, 1], [2], [3], False)]
            sage: T.cylinders(RED)
            []

        Some examples in Q(4, -1^8)::

            sage: T = VeeringTriangulation("(0,1,2)", "BBR")
            sage: T.cylinders(BLUE)
            [([0, 2], [], [4], True)]
            sage: T.cylinders(RED)
            []

            sage: fp = "(5,4,7)(~5,3,10)(1,~0,8)(~1,~4,11)(2,6,9)(~2,0,12)"
            sage: cols = "BBBBBBBRRRRRR"
            sage: T = VeeringTriangulation(fp, cols, mutable=True)
            sage: T.cylinders(BLUE)
            [([12, 4, 0, 2, 9, 10, 6], [18, 16, 14], [24, 22, 20], True)]
            sage: T.cylinders(RED)
            []
            sage: T.forgot_forward_flippable_colour()
            sage: T.cylinders(RED)
            [([24, 5, 18], [12], [0], True),
             ([16, 2, 22], [9], [1], True),
             ([20, 11, 14], [8], [6], True)]

            sage: fp = "(0,12,3)(1,2,11)(4,6,7)(5,~2,10)(8,~5,~4)(9,~1,~0)"
            sage: cols = "BBRRRBBBBRRRB"
            sage: T = VeeringTriangulation(fp, cols)
            sage: T.cylinders(BLUE)
            [([12, 14], [], [8], True)]
            sage: T.cylinders(RED)
            [([20, 5, 22], [10], [2], True)]

            sage: fp = '(0,~5,4)(1,~3,2)(3,5,~4)(6,~1,~0)'
            sage: cols = 'RBBRBRB'
            sage: T = VeeringTriangulation(fp, cols)
            sage: T.cylinders(BLUE)
            [([12, 3, 4], [7], [1], True)]
            sage: T.cylinders(RED)
            []
            sage: T = VeeringTriangulation("(0,~2,1)(2,~4,3)(4,~6,5)(6,~1,~0)", "RBRBBBR")
            sage: T.cylinders(BLUE)
            [([10, 8, 6], [], [13, 4], True)]

        Torus with PURPLE edge::

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "PBR", mutable=True)
            sage: T.cylinders(RED)
            [([4, 1], [2], [3], False)]
            sage: T.cylinders(BLUE)
            [([0, 3], [4], [5], False)]
            sage: R = T.copy()
            sage: R.set_colour(RED)
            sage: R.cylinders(RED)
            [([4, 1], [2], [3], False)]

            sage: B = T.copy()
            sage: B.set_colour(BLUE)
            sage: B.cylinders(BLUE)
            [([0, 3], [4], [5], False)]

        Longer examples::

            sage: fp = "(~0,5,1)(~1,6,2)(~2,3,9)(~3,4,8)(~4,7,0)"
            sage: cols = "BBBBBRRRRR"
            sage: T = VeeringTriangulation(fp, cols, mutable=True)
            sage: T.cylinders(BLUE)
            [([0, 2, 4, 6, 8], [14, 10, 12], [18, 16], False)]
            sage: T.forgot_forward_flippable_colour()
            sage: T.cylinders(BLUE)
            [([0, 2, 4, 6, 8], [14, 10, 12], [18, 16], False)]
            sage: T.set_colour(BLUE)
            sage: T.rotate()
            sage: T.cylinders(RED)
             [([0, 2, 4, 6, 8], [14, 10, 12], [18, 16], False)]

            sage: V = VeeringTriangulation("(0,3,8)(1,~4,2)(4,5,~11)(6,~5,7)(9,~8,11)(10,~2,~1)(~10,~7,~9)(~6,~0,~3)", "PBPBRPRBRBRB")
            sage: V.cylinders(BLUE)
            [([0, 7], [16], [13], False),
             ([4, 3], [9], [20], False),
             ([10, 14, 19, 22], [8, 17], [12, 21], False)]


            sage: V = VeeringTriangulation("(0,12,~11)(1,13,~12)(2,3,14)(4,10,9)(5,~10,11)(6,~5,~17)(7,~0,~6)(8,~4,~7)(15,~13,~14)(16,17,~2)(~16,~3,~15)(~9,~8,~1)", "RRRBRRBBBBPBBBRRPB")
            sage: V.cylinders(BLUE)
            []

        Some examples with boundaries::

            sage: fp = "(0,2,1)(~0,3,~1)"
            sage: bdry = "(~2:2,~3:2)"
            sage: for cols in ["BRRR", "BBRR", "RBRR"]:
            ....:     vt = VeeringTriangulation(fp, bdry, cols)
            ....:     print(cols, vt.cylinders(RED), vt.cylinders(BLUE))
            BRRR [] []
            BBRR [] [([2, 1], [4], [6], False)]
            RBRR [] []
        """
        if col != RED and col != BLUE:
            raise ValueError("'col' must be RED or BLUE")

        opcol = RED if col == BLUE else BLUE

        n = 2 * self._ne
        fp = self._fp
        ep = self._ep
        cols = self._colouring

        cylinders = []

        seen = [False] * n
        for a in range(n):
            if fp[a] == -1 or seen[a] or self._bdry[a]:
                continue

            # triangle (a,b,c)
            b = fp[a]
            c = fp[b]
            if seen[b] or seen[c]:
                continue

            if (cols[a // 2] == opcol) + (cols[b // 2] == opcol) + (cols[c // 2] == opcol) > 1:
                seen[a] = seen[b] = seen[c] = True
                continue

            # We normalize the edges (a,b,c) so that a is the one going forward
            # (each triangle in a cylinder has two "doors" and one "boundary"). We
            # choose a traversal order in the triangle and hence have two types of
            # triangles.
            #
            #  right triangle       left triangle
            #
            #       x               x---------x
            #      / \               \    b  /
            #     /b  \ -->           \c    /  -->
            #    /    a\               \  a/
            #   /  c    \               \ /
            #  x---------x               x
            #
            # We make it so we start with a right triangle.
            if cols[a // 2] == opcol:
                a, b, c = b, c, a
            elif cols[b // 2] == opcol:
                a, b, c = c, a, b
            assert cols[a // 2] == col or cols[a // 2] == PURPLE
            assert cols[b // 2] == col or cols[b // 2] == PURPLE
            assert cols[c // 2] == opcol
            a0, b0, c0 = a, b, c
            RIGHT = 0
            LEFT = 1
            typ = RIGHT

            cc = []    # cycle of edges inside the cylinder
            rbdry = [] # right boundary
            lbdry = [] # left boundary
            half_turn = False # whether the cylinder is a folded cylinder
            cyl = True
            while not seen[a] and not self._bdry[a]:
                assert cols[a // 2] == col or cols[a // 2] == PURPLE, (typ, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                seen[a] = seen[ep(a)] = True
                cc.append(a)
                if typ == RIGHT:
                    assert cols[c // 2] == opcol, (typ, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                    assert cols[b // 2] == col or cols[b // 2] == PURPLE, (typ, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                    rbdry.append(c)
                else:
                    assert cols[b // 2] == opcol, (typ, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                    assert cols[c // 2] == col or cols[c // 2] == PURPLE, (typ, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                    lbdry.append(b)

                if a == ep(a):
                    # found a folded edge... we can not continue in this
                    # direction. Either stop or start again from the other door.
                    if half_turn:
                        cyl = True
                        break
                    half_turn = True
                    cc = [ep(x) for x in reversed(cc)]
                    lbdry.reverse()
                    rbdry.reverse()
                    rbdry, lbdry = lbdry, rbdry
                    lbdry.pop()  # a0 will be added again at the beginning of next loop
                    assert cols[c0 // 2] == opcol
                    a, b, c = b0, c0, a0
                    typ = LEFT
                    continue

                # go to triangle across the door
                a = ep(a)
                if self._bdry[a]:
                    cyl = False
                    break
                else:
                    b = fp[a]
                    c = fp[b]
                    assert cols[a // 2] == col or cols[a // 2] == PURPLE, (self, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                    if cols[b // 2] == col or cols[b // 2] == PURPLE:
                        assert cols[c // 2] == opcol, (self, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                        # LEFT type, next door is  b
                        a, b, c = b, c, a
                        typ = LEFT
                    elif cols[c // 2] == col or cols[c // 2] == PURPLE:
                        assert cols[b // 2] == opcol, (self, a, colour_to_string(cols[a // 2]), b, colour_to_string(cols[b // 2]), c, colour_to_string(cols[c // 2]))
                        # RIGHT type, next door is c
                        a, b, c = c, a, b
                        typ = RIGHT
                    else:
                        cyl = False
                        break

            if cyl and (a == a0 or half_turn):
                cylinders.append((cc, rbdry, lbdry, half_turn))

        return cylinders

    def cylinder_is_minimal(self, cyl):
        r"""
        Return whether ``cyl`` is minimal, that is whether all saddle connection
        appearing in its boundary are colinear.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, RED
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRRRRB")
            sage: cyl0, cyl1 = vt.cylinders(RED)
            sage: cyl0
            ([0, 3], [4], [6], False)
            sage: cyl1
            ([8, 12, 15, 11], [5, 16], [7, 17], False)
            sage: vt.cylinder_is_minimal(cyl0)
            True
            sage: vt.cylinder_is_minimal(cyl1)
            False
        """
        gens = self.generators_matrix()
        mid_half_edges, rbdry, lbdry, pocket = cyl

        rbdry = gens.matrix_from_columns([i // 2 for i in rbdry])
        lbdry = gens.matrix_from_columns([i // 2 for i in lbdry])
        return is_rank_one(rbdry) and is_rank_one(lbdry)

    def cylinder_circumference(self, cyl, x, check=True):
        r"""
        Return the circumference of the cylinder ``x`` in coordinates ``x``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, RED
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRRRRB")
            sage: cyl0, cyl1 = vt.cylinders(RED)
            sage: gens = vt.generators_matrix()
            sage: x = (5, 9, 4, 4, 1, 5, 5, 6, 1)
            sage: vt.cylinder_circumference(cyl0, x)
            4
            sage: vt.cylinder_circumference(cyl1, x)
            5

            sage: x = (12, 9, 4, 4, 1, 5, 5, 6, 1)
            sage: print(vt.cylinder_circumference(cyl0, x))
            Traceback (most recent call last):
            ...
            AssertionError: does not satisfy train-track constraints
        """
        if check:
            if len(x) != self._ne:
                raise ValueError("x must be a list or a vector of length the number of edges")
            self._set_subspace_constraints(self._constraint_check, x, VERTICAL)

        middle, rbdry, lbdry, pocket = cyl
        if pocket:
            raise "NotImplementedError"
        circ = 0
        for h in middle:
            e = h // 2
            if self.is_forward_flippable(e):
                circ += x[e]
            elif self.is_backward_flippable(e):
                circ -= x[e]
        return circ

    def cylinder_area(self, cyl, x, y, check=True):
        r"""
        Return the area of the cylinder ``cyl`` for the coordinates ``x`` and ``y``.

        Warning: this does not return the area of the flat cylinder but rather
        the sum of areas of the triangles in the combinatorial cylinder. The
        former might be smaller. They coincide when the cylinder is minimal
        (see :meth:`cylinder_is_minimal`).

        The area is a quadratic form and ``x`` and ``y`` are not required to be
        non-negative. Simply to satisfy the triangle inequalities (and possibly
        additional linear constraints).

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, RED
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRRRRB")
            sage: cyl0, cyl1 = vt.cylinders(RED)
            sage: gens = vt.generators_matrix()
            sage: x = (5, 9, 4, 4, 1, 5, 5, 6, 1)
            sage: y = (5, 1, 4, 4, 9, 5, 5, 4, 1)
            sage: vt.cylinder_area(cyl0, x, y)
            40
            sage: vt.cylinder_area(cyl1, x, y)
            50

            sage: x = (12, 9, 4, 4, 1, 5, 5, 6, 1)
            sage: y = (5, 1, 4, 4, 9, 5, 5, 4, 1)
            sage: print(vt.cylinder_area(cyl0, x, y))
            Traceback (most recent call last):
            ...
            AssertionError: does not satisfy train-track constraints
        """
        if check:
            if len(x) != self._ne or len(y) != self._ne:
                raise ValueError("x and y must be lists or vectors of length the number of edges")
            self._set_subspace_constraints(self._constraint_check, x, VERTICAL)
            self._set_subspace_constraints(self._constraint_check, y, HORIZONTAL)

        middle, rbdry, lbdry, pocket = cyl
        area = 0
        for a in middle:
            b = self._fp[a]
            c = self._fp[b]
            if self.half_edge_colour(a) == BLUE and self.half_edge_colour(b) == RED:
                a, b, c = c, a, b
            elif self.half_edge_colour(c) == BLUE and self.half_edge_colour(a) == RED:
                a, b, c = b, c, a
            assert self.half_edge_colour(b) == BLUE and self.half_edge_colour(c) == RED
            xl = x[b // 2]
            yl = y[b // 2]
            xr = x[c // 2]
            yr = y[c // 2]
            area += xr * yl + xl * yr
        return area /2

    def dehn_twists(self, col):
        r"""
        Return the list of Dehn twists along the cylinders of colour ``col``.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, BLUE, RED

            sage: T = VeeringTriangulation("(0,~4,5)(1,~0,6)(2,8,~1)(3,~7,~2)(4,~3,7)(~8,9,~11)(10,~5,~9)(11,~6,~10)", "BBBBBRRRRBBB", mutable=True)
            sage: b1, b2 = T.dehn_twists(BLUE)
            sage: b1
            VeeringFlipSequence(VeeringTriangulation("(0,~4,5)...(~8,9,~11)", "BBBBBRRRRBBB"), "1B 0B 4B 2B 1B 0B", "(0,3,1,4,~2)(~0,~3,~1,~4,2)")
            sage: b2
            VeeringFlipSequence(VeeringTriangulation("(0,~4,5)...(~8,9,~11)", "BBBBBRRRRBBB"), "9B 10B", "(9,~10,11)(~9,10,~11)")

            sage: T.rotate()
            sage: r1, r2 = T.dehn_twists(RED)
            sage: r1
            VeeringFlipSequence(VeeringTriangulation("(0,~4,5)...(~8,9,~11)", "RRRRRBBBBRRR"), "3R 4R 0R 2R 3R 4R", "(0,2,4,1,3)(~0,~2,~4,~1,~3)")
            sage: r2
            VeeringFlipSequence(VeeringTriangulation("(0,~4,5)...(~8,9,~11)", "RRRRRBBBBRRR"), "11R 10R", "(9,11,10)(~9,~11,~10)")

        A (purple) square-tiled surface corresponds to a Penner system. A
        product associated to the Dehn twists is of pseudo-Anosov type if and
        only if all twists appear at least once::

            sage: T = VeeringTriangulation("(0,~2,1)(2,~11,~3)(3,10,~4)(4,~15,~5)(5,14,~6)(6,~10,~7)(7,9,~8)(8,17,~9)(11,15,~12)(12,~17,~13)(13,~16,~14)(16,~1,~0)", "PRBPRBPRBPBRBPRPBR")
            sage: b1, b2 = T.dehn_twists(BLUE)
            sage: r1, r2, r3 = T.dehn_twists(RED)

            sage: (r1 * r3 * b1 * b2).is_pseudo_anosov()
            False
            sage: (r1 * r3 * b1 * b2 * r2).is_pseudo_anosov()
            True
        """
        if self.has_folded_edge():
            raise NotImplementedError

        if col != RED and col != BLUE:
            raise ValueError("'col' must be RED or BLUE")

        from .flip_sequence import VeeringFlipSequence
        twists = []

        opcol = BLUE if col == RED else RED
        vp = self._vp
        ep = self._ep
        cols = self._colouring
        for mid, rbdry, lbdry, half in self.cylinders(col):
            assert not half

            # count packets
            edges = []
            packets = []
            p = []
            for h in lbdry:
                assert cols[h // 2] == opcol
                s = vp[h]
                p.clear()
                while cols[s // 2] != opcol:
                    p.append(s // 2)
                    s = vp[s]
                edges.extend(p)
                packets.append(len(p))

            # build the flip sequence
            F = VeeringFlipSequence(self)
            m = len(lbdry)
            n = len(edges)
            flipsmod2 = [0] * n
            for shift in range(m):
                j = shift if col == BLUE else -shift
                for i in range(m):
                    K = range(packets[i] - 1, 0, -1) if col == BLUE else range(0, packets[i] - 1, 1)
                    for k in K:
                        l = (j + k) % n
                        F.append_flip(edges[l], col)
                        flipsmod2[l] = 1 - flipsmod2[l]
                    j += packets[i]

            # build the relabelling
            r = perm_id(2 * self._ne)
            vp1 = F._start._vp
            cols1 = F._start._colouring
            vp2 = F._end._vp
            cols2 = F._end._colouring
            for h in lbdry:
                assert cols1[h // 2] == cols2[h // 2] == opcol
                s1 = vp1[h]
                s2 = vp2[h]
                assert cols1[s1 // 2] == cols2[s2 // 2]
                assert cols1[s1 // 2] != opcol
                while cols1[s1 // 2] != opcol:
                    r[s2] = s1
                    r[s2 ^ 1] = s1 ^ 1
                    s1 = vp1[s1]
                    s2 = vp2[s2]
                    assert cols1[s1 // 2] == cols2[s2 // 2]
                assert s1 == s2

            # check
            for i in range(n):
                j = (i - m) % n if col == BLUE else (i + m) % n
                e = edges[i]
                f = edges[j]
                assert r[2 * e] // 2 == f and r[2 * e + 1] // 2 == f

            F.append_relabelling(r)

            # TODO: remove assertion check
            assert F.start() == F.end(), (F.start(), F.end(), F.start().is_isomorphic_to(F.end(), certificate=True))

            twists.append(F)

        return twists

    def is_cylindrical(self, col=None):
        r"""
        Return whether this veering triangulation is cylindrical.

        A Veering triangulation is blue cylindrical (resp red cylindrical) if
        all its triangles have two blue edges (resp red). Here a purple edge
        counts for both blue and red.

        It is purple cylindrical if all its triangle are adjacent to a purple
        edge. This is equivalent to say that both the red and blue colouring
        of the purple edges are respectively red and blue cylindrical

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", mutable=True)
            sage: T.is_cylindrical()
            True

            sage: T.forgot_forward_flippable_colour()
            sage: T.is_cylindrical(PURPLE)
            True
            sage: T.is_cylindrical(RED)
            True
            sage: T.is_cylindrical(BLUE)
            True

            sage: T = VeeringTriangulation("(0,3,4)(1,~3,5)(2,6,~4)", "PPPBRRB")
            sage: T.is_cylindrical(PURPLE)
            True
        """
        if col is None:
            return self.is_cylindrical(PURPLE) or self.is_cylindrical(BLUE) or self.is_cylindrical(RED)
        elif col != BLUE and col != RED and col != PURPLE:
            raise ValueError("'col' must be one of BLUE, RED or PURPLE")

        n = 2 * self._ne
        fp = self._fp
        cols = self._colouring
        seen = [False] * n
        for a in range(n):
            if fp[a] == -1 or seen[a]:
                continue
            b = fp[a]
            c = fp[b]
            seen[a] = seen[b] = seen[c] = True
            if col == PURPLE:
                if cols[a // 2] != PURPLE and cols[b // 2] != PURPLE and cols[c // 2] != PURPLE:
                    return False
            else:
                if (cols[a // 2] == PURPLE) + (cols[b // 2] == PURPLE) + (cols[c // 2] == PURPLE) + \
                   (cols[a // 2] == col) + (cols[b // 2] == col) + (cols[c // 2] == col) != 2:
                    return False
        return True

    def is_quadrangulable(self):
        k = 0
        fp = self._fp
        for e in range(self._ne):
            if not self.is_forward_flippable(e, check=False):
                continue

            k += 1 + (self._fp[2 * e + 1] != -1)

        return k == self.num_faces()

    def is_square_tiled(self, col=PURPLE):
        r"""
        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBR")
            sage: T.is_square_tiled(BLUE)
            False
            sage: T.is_square_tiled(RED)
            True
            sage: T.is_cylindrical()
            True

            sage: T = VeeringTriangulation("(0,1,4)(~1,2,5)(~2,~4,3)(~3,~5,~0)", "RRRRBB")
            sage: T.is_square_tiled()
            False
            sage: T.is_cylindrical()
            True

            sage: T = VeeringTriangulation("(~0,1,4)(~1,~4,2)(~2,3,5)(~3,6,0)", "RRRRBBB")
            sage: T.is_square_tiled(RED)
            True
            sage: T.is_square_tiled(BLUE)
            False
            sage: T.is_cylindrical()
            True

            sage: T = VeeringTriangulation("(0,1,2)", "RRB")
            sage: T.is_square_tiled(RED)
            True
            sage: T.is_square_tiled(BLUE)
            False
            sage: T.is_cylindrical()
            True

            sage: T = VeeringTriangulation("(1,~3,2)(~2,0,3)", "RRRB")
            sage: T.is_square_tiled(RED)
            True
            sage: T.is_square_tiled(BLUE)
            False
            sage: T.is_cylindrical()
            True
        """
        k = 0
        fp = self._fp
        for e in range(self._ne):
            if not self.is_forward_flippable(e):
                continue
            if self.edge_colour(e) != col:
                return False

            k += 1 + (fp[2 * e + 1] != -1)

        return k == self.num_faces()

    def is_strebel(self, slope=VERTICAL):
        r"""
        Return whether this veering triangulation is Strebel.

        A veering triangulation is Strebel if it has no forward flippable edge.

        EXAMPLES::

            sage: from veerer import *

        We consider below the six veering triangulations of the stratum H_1(2,
        -2) that have two triangles::

            sage: t = Triangulation("(0,2,1)(3,~1,~0)", boundary="(~3:2,~2:2)")
            sage: vtB0 = VeeringTriangulation(t, "RRBB")
            sage: vtB1 = VeeringTriangulation(t, "RBBB")
            sage: vtB2 = VeeringTriangulation(t, "BRBB")
            sage: vtR0 = VeeringTriangulation(t, "BBRR")
            sage: vtR1 = VeeringTriangulation(t, "BRRR")
            sage: vtR2 = VeeringTriangulation(t, "RBRR")

            sage: all(vt.is_strebel(VERTICAL) for vt in [vtB1, vtR2])
            True
            sage: any(vt.is_strebel(VERTICAL) for vt in [vtB0, vtB2, vtR0, vtR1])
            False

            sage: all(vt.is_strebel(HORIZONTAL) for vt in [vtB2, vtR1])
            True
            sage: any(vt.is_strebel(HORIZONTAL) for vt in [vtB0, vtB1, vtR0, vtR2])
            False
        """
        ep = self._ep
        n = 2 * self._ne
        if slope == VERTICAL:
            return not any(self.is_forward_flippable(e, check=False) for e in range(self._ne) if not self._bdry[2 * e] and not self._bdry[ep(2 * e)])
        elif slope == HORIZONTAL:
            return not any(self.is_backward_flippable(e, check=False) for e in range(self._ne) if not self._bdry[2 * e] and not self._bdry[ep(2 * e)])
        else:
            raise ValueError('slope must either be HORIZONTAL or VERTICAL')

    def properties_code(self):
        r"""
        Return an integer code that gathers boolean properties of this veering
        triangulation.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.constants import properties_to_string
            sage: T = VeeringTriangulation("(0,1,8)(2,~7,~1)(3,~0,~2)(4,~5,~3)(5,6,~4)(7,~8,~6)", "BRRRRBRBR")
            sage: T.properties_code()
            17
            sage: properties_to_string(81)
            'red geometric'
        """
        from .constants import BLUE, RED, SQUARETILED, QUADRANGULABLE, GEOMETRIC

        code = 0
        if self.is_square_tiled(RED):
            code |= SQUARETILED
            code |= RED
        if self.is_square_tiled(BLUE):
            code |= SQUARETILED
            code |= BLUE
        if self.is_quadrangulable():
            code |= QUADRANGULABLE
        if self.is_cylindrical(RED):
            code |= RED
        if self.is_cylindrical(BLUE):
            code |= BLUE
        if self.is_delaunay():
            code |= GEOMETRIC

        if code & BLUE and code & RED:
            raise RuntimeError("found a blue and red triangulations!")
        if code & SQUARETILED:
            if not code & BLUE and not code & RED:
                raise RuntimeError("square-tiled should be coloured")
            if not code & GEOMETRIC:
                raise RuntimeError("square-tiled should be geometric")

        return code

    def residue_matrix(self, slope=VERTICAL):
        r"""
        Return the matrix of residues.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, StrebelGraph, VERTICAL, HORIZONTAL

            sage: vt = VeeringTriangulation("(0,1,2)(~1,~2,3)", "(~0:1)(~3:1)", "RBRR")
            sage: r = vt.residue_matrix()
            sage: r
            [-1  0  0  0]
            [ 0  0  0  1]

            sage: G = StrebelGraph("(0,2,~3,~1)(1)(3,~0)(~2)")
            sage: for colouring in G.colourings():
            ....:     for vt in G.veering_triangulations(colouring):
            ....:         for slope in [VERTICAL, HORIZONTAL]:
            ....:             r = vt.residue_matrix(slope)
            ....:             for x in vt.generators_matrix(slope).rows():
            ....:                 assert sum(r * x) == 0, (vt, slope, x)

        Some quadratic differentials with double poles::

            sage: VeeringTriangulation("(~2,4,5)(~3,6,~4)(0:1)(1:1,2:1,3:1)(~5:1,7:1)(~6:1,~7:1)", "BBBBRBBB").residue_matrix()
            [1 0 0 0 0 0 0 0]
            [0 1 1 1 0 0 0 0]
            [0 0 0 0 0 1 0 1]
            [0 0 0 0 0 0 1 1]
        """
        ne = self._ne
        colouring = self._colouring

        if any(col == PURPLE or col == GREEN for col in colouring):
            raise NotImplementedError

        is_abelian, orientations = self.is_abelian(certificate=True)
        if is_abelian:
            # Abelian differential: we make a consistent global choice of signs for the residues
            nf = self.num_boundary_faces()
            r = matrix(ZZ, nf, ne)
            if slope == VERTICAL:
                orientations = [1 if x else -1 for x in orientations]
            elif slope == HORIZONTAL:
                orientations = [1 if (orientations[i] == (colouring[i // 2] == RED)) else -1 for i in range(2 * ne)]
            else:
                raise ValueError('invalid slope argument; must be VERTICAL or HORIZONTAL')

            for i, f in enumerate(self.boundary_faces()):
                for h in f:
                    r[i, h // 2] += orientations[h]

        else:
            # quadratic differentials: we can only have a local choice of signs
            # Note that faces whose angle is an odd multiple of pi have residue zero and we
            # ignore them
            fp = self._fp
            even_angle_faces = [f for f in self.boundary_faces() if self.face_angle(f[0]) % 2 == 0]
            r = matrix(ZZ, len(even_angle_faces), ne)
            for i, f in enumerate(even_angle_faces):
                o = 1
                for h0 in f:
                    r[i, h0 // 2] += o

                    h1 = fp[h0]
                    if self.half_edge_num_separatrices(h1, slope) % 2 == 0:
                        o *= -1

        return r

    def add_residue_constraints(self, residue_constraints):
        r"""
        Return the veering triangulation linear family obtained by adding the
        given linear constraints on the residues.

        Note that the resulting linear family might not intersect the relative
        interior of the coordinates (respectively Delaunay) cone. To check
        whether this is the case, use the method ``is_core`` (resp.
        ``is_delaunay``).

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,5,~4)(2,6,~5)(3,~0,7)(4,~3,~1)(1:1)(~7:1)(~6:1)(~2:1)", colouring="RRRBBBBB")
            sage: f1 = vt.add_residue_constraints([[1, 0, 1, 1]])
            sage: f1
            VeeringTriangulationLinearFamily("(0,5,~4)(~0,7,3)(~1,4,~3)(2,6,~5)(1:1)(~2:1)(~6:1)(~7:1)", "RRRBBBBB", [(1, 0, 0, 0, 0, 1, 1, 1), (0, 1, 0, 0, 1, 1, 1, 0), (0, 0, 0, 1, 1, 1, 1, 1)])
            sage: f1.is_core()
            True
            sage: f1.is_delaunay()
            True

            sage: f2 = vt.add_residue_constraints([[1, 1, 0, 1]])
            sage: f2
            VeeringTriangulationLinearFamily("(0,5,~4)(~0,7,3)(~1,4,~3)(2,6,~5)(1:1)(~2:1)(~6:1)(~7:1)", "RRRBBBBB", [(1, 0, 0, -1, -1, 0, 0, 0), (0, 1, 0, -1, 0, 0, 0, -1), (0, 0, 1, -1, -1, -1, 0, -1)])
            sage: f2.is_core()
            False

        Adding residue constraints commute with taking the Strebel graph
        (modulo a possible relabelling of the residue)::

            sage: G1 = f1.strebel_graph().add_residue_constraints([[1, 1, 0, 1]])
            sage: G2 = f1.add_residue_constraints([[0, 1, 1, 1]]).strebel_graph()
            sage: assert G1 == G2, (G1, G2)
        """
        if not isinstance(residue_constraints, Matrix):
            residue_constraints = matrix(residue_constraints)

        base_ring = cm.common_parent(self.base_ring(), residue_constraints.base_ring())
        orig_constraints_matrix = self.constraints_matrix()
        n1 = orig_constraints_matrix.nrows()
        n2 = residue_constraints.nrows()
        constraints_matrix = matrix(base_ring, n1 + n2, self.num_edges())
        constraints_matrix[:n1, :] = orig_constraints_matrix
        constraints_matrix[n1:, :] = residue_constraints * self.residue_matrix()
        gens = constraints_matrix.right_kernel_matrix()
        from .linear_family import VeeringTriangulationLinearFamily
        return VeeringTriangulationLinearFamily(self, gens)

    def flip_back(self, e, col, Lx=None, Gx=None, check=True):
        r"""
        Flip backward an edge in place

        EXAMPLES::

            sage: from veerer import *

            sage: T0 = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])
            sage: T = T0.copy(mutable=True)
            sage: T.flip(1, RED)
            sage: T.flip(0, RED)
            sage: T.flip_back(0, RED)
            sage: T.flip_back(1, RED)
            sage: T == T0
            True

            sage: T.flip(1, BLUE)
            sage: T.flip(2, BLUE)
            sage: T.flip_back(2, BLUE)
            sage: T.flip_back(1, RED)
            sage: T == T0
            True

        Some examples involving linear subspaces::

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: T = T.copy(mutable=True)
            sage: Gx = matrix(ZZ, [s, t])
            sage: Gx.echelon_form()
            [1 0 0 1 1 1 1]
            [0 1 1 1 1 1 0]
            sage: T.flip(3, 2, Gx=Gx)
            sage: T.flip(4, 2, Gx=Gx)
            sage: T.flip(5, 2, Gx=Gx)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(0), VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(1), VERTICAL)
            sage: Gx.echelon_form()
            [ 1  0  0  1  1  1  1]
            [ 0  1  1 -1 -1 -1  0]
            sage: T.flip_back(5, 2, Gx=Gx)
            sage: T.flip_back(4, 2, Gx=Gx)
            sage: T.flip_back(3, 2, Gx=Gx)
            sage: Gx.echelon_form()
            [1 0 0 1 1 1 1]
            [0 1 1 1 1 1 0]
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        if check:
            if col != BLUE and col != RED and col != PURPLE:
                raise ValueError("'col' must be BLUE, RED or PURPLE")

            e = self._check_edge(e)
            if not self.is_backward_flippable(e, check=False):
                raise ValueError('half-edge e={} is not backward flippable'.format(e))
        h = 2 * e

        if Lx is not None:
            raise NotImplementedError("not implemented for linear equations")

        H = self._ep(h)

        Triangulation.flip_back(self, e, check=False)
        old_col = self._colouring[e]
        self._colouring[e] = col

        if Gx is not None:
            a, b, c, d = self.square_about_half_edge(h, check=False)
            a //= 2
            b //= 2
            c //= 2
            d //= 2
            Gx.add_multiple_of_column(e, e, -1)
            Gx.add_multiple_of_column(e, a, +1)
            Gx.add_multiple_of_column(e, b, +1)

    def intersection_form(self):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,3,8)(~0,5,6)(~3,4,2)(~4,1,7)", "BBBRRRRRR")
            sage: I = vt.intersection_form()
            sage: I
            [ 0  0  0  1  0  1  0  0  0]
            [ 0  0  0  0  0  0  0  1  0]
            [ 0  0  0  1  0  0  0  0  0]
            [-1  0 -1  0  0  0  0  0  0]
            [ 0  0  0  0  0  0  0  0  0]
            [-1  0  0  0  0  0  0  0  0]
            [ 0  0  0  0  0  0  0  0  0]
            [ 0 -1  0  0  0  0  0  0  0]
            [ 0  0  0  0  0  0  0  0  0]
        """
        if any(c == PURPLE or c == GREEN for c in self._colouring):
            raise NotImplementedError

        if any(self._bdry):
            raise NotImplementedError

        m = matrix(ZZ, self._ne)
        for a, b, c in self.non_degenerate_triangles():
            b //= 2
            c //= 2
            m[b, c] = 1
            m[c, b] = -1
        return m

    def relative_generators_matrix(self):
        r"""
        EXAMPLES::

            sage: from veerer import *

            sage: VeeringTriangulation("(0,~5,4)(~0,~2,3)(1,2,5)(~1,~3,~4)", "RRBBRB").relative_generators_matrix().echelon_form()
            [ 1 -1  0 -1  0  1]
            sage: VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,3,8)(~1,~6,~7)(2,~8,7)(~2,~3,4)", "RRRBBBBRB").relative_generators_matrix().echelon_form()
            []
            sage: VeeringTriangulation("(0,~5,~4)(~0,7,9)(1,5,~7)(~1,10,~9)(2,11,~6)(~2,~11,8)(3,~8,~10)(~3,6,4)", "RRBBBRRBRRBR").relative_generators_matrix().echelon_form()
            [ 1 -1  2 -1 -1  0  0  1  0  0 -1 -2]
        """
        if any(self._bdry):
            raise NotImplementedError

        G = self.generators_matrix()
        I = G * self.intersection_form() * G.transpose()
        return I.right_kernel_matrix() * G

    def relative_dimension(self):
        return self.relative_generators_matrix().nrows()

    def rank(self):
        r"""
        EXAMPLES::

            sage: from veerer import *

        An example in Q_0(2, -1^6)::

            sage: VeeringTriangulation("(0,3,8)(~0,5,6)(~3,4,2)(~4,1,7)", "BBBRRRRRR").rank()
            2

        Abelian principal stratum in genus 3::

            sage: vt = VeeringTriangulation("(0,16,~15)(~0,~14,15)(1,19,~18)(~1,~23,8)(2,22,~21)(~2,~8,9)(3,21,~20)(~3,~9,10)(4,20,~19)(~4,~10,11)(5,23,~22)(~5,~11,12)(6,18,~17)(~6,~12,13)(7,17,~16)(~7,~13,14)", "RRRRRRRRBBBBBBBBBBBBBBBB")
            sage: vt.rank()
            3

        A Teichmueller curve in Q_0(1, -1^5)::

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(T, [s, t])
            sage: f.rank()
            1

        An eigenform locus in Q_0(2, -1^6)::

            sage: X9 = VeeringTriangulationLinearFamilies.prototype_H1_1(0, 2, 1, -1)
            sage: X9.rank()
            1

        Gothic locus::

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,~0)(5,6,~1)(7,~2,8)(9,~3,~6)(10,~7,~4)(11,~5,12)(13,14,~8)(15,~9,16)(17,18,~10)(19,~17,~11)(20,~13,~12)(21,~14,~18)(22,~21,~15)(23,24,~16)(25,~23,~19)(26,~20,~25)(~26,~24,~22)", "RBBRBRBRRBRBBRBBRRBRRRBBRRB")
            sage: subspace = [(1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1, 0, 0, 0, -1, 1, 1, 0, 0, -1, 1, 0, -1),
            ....:             (0, 1, 1, 0, 0, 1, 2, 0, -1, 2, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0, 1),
            ....:             (0, 0, 0, 1, 1, 1, 1, 0, 0, 0, -1, 1, 2, 2, 2, 1, 1, 0, 1, -1, 0, 1, 0, 1, 0, 0, 0),
            ....:             (0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 2, 1, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 0)]
            sage: f = VeeringTriangulationLinearFamily(vt, subspace)
            sage: f.rank()
            2

        An eigenform locus in Q_1(2, 1, -1^3)::

            sage: f = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,6,7)(~4,8,9)(~5,~7,10)(~9,~10,11)", "RRBBBRRBRRBR", [(1, 0, -1, -1, 0, -1, -2, -3, 0, 0, -2, 2), (0, 1, 1, 1, 0, 1, 2, 3, 2, 2, 2, 0), (0, 0, 0, 0, 1, -1, -2, -2, -2, -1, -1, 0)])
            sage: f.rank()
            1

        TESTS:

        These Abelian examples used to be wrong::

            sage: VeeringTriangulation("(0,~5,4)(~0,~2,3)(1,2,5)(~1,~3,~4)", "RRBBRB").rank()
            1
            sage: VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,3,8)(~1,~6,~7)(2,~8,7)(~2,~3,4)", "RRRBBBBRB").rank()
            2
            sage: VeeringTriangulation("(0,3,2)(~0,4,7)(1,~2,~7)(~1,~3,~6)(~4,~5,~8)(5,8,6)", "BBRRRBRRR").rank()
            2
            sage: VeeringTriangulation("(0,~5,~4)(~0,7,9)(1,5,~7)(~1,10,~9)(2,11,~6)(~2,~11,8)(3,~8,~10)(~3,6,4)", "RRBBBRRBRRBR").rank()
            2
            sage: VeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)(~2,7,8)(~3,10,9)(~4,11,~8)(~5,12,13)(~6,14,15)(~7,~9,~14)(~10,16,~11)(~12,17,18)(~13,19,20)(~15,~18,~20)(~16,~17,~19)", "BRRRRRBRBBBRBRRRRRBBR").rank()
            4
        """
        absolute_dimension = self.dimension() - self.relative_dimension()
        if absolute_dimension % 2:
            raise ValueError("odd-dimensional intersection with absolute cohomology")
        return absolute_dimension // 2

    def _set_train_track_constraints_fast(self, cs, L, slope):
        zero = L.base_ring().zero()
        one = L.base_ring().one()
        m_one = -one
        ne = self.num_edges()
        if slope == VERTICAL:
            shift = 0
        elif slope == HORIZONTAL:
            shift = ne
        else:
            raise ValueError("invalid slope parameter; must be VERTICAL or HORIZONTAL")

        # switch
        for (i, j, k) in self.degenerate_triangles(slope):
            # i is degenerate
            # x[i] = 0
            # x[j] - x[k] = 0
            cs.insert(L.element_class(L, {shift + i // 2: one}, zero) == zero, check=False)
            cs.insert(L.element_class(L, {shift + j // 2: one, shift + k // 2: m_one}, zero) == zero, check=False)

        for (i, j, k) in self.non_degenerate_triangles(slope):
            # i is large
            # x[i] - x[j] - x[k] == 0
            cs.insert(L.element_class(L, {shift + i // 2: one, shift + j // 2: m_one, shift + k // 2: m_one}, zero) == zero, check=False)

        # non-negativity
        for e in range(ne):
            cs.insert(L.element_class(L, {shift + e: one}, zero) >= zero, check=False)

    def _set_subspace_constraints(self, insert, x, slope=VERTICAL):
        r"""
        Set the linear parts of the train-track equations

        INPUT:

        - ``insert`` - a function to be called for each equation

        - ``x`` - variable factory (the variable for edge ``e`` is constructed
          via ``x[e]``)

        - ``slope`` - (default ``VERTICAL``) the slope of the train-track
          ``HORIZONTAL`` or ``VERTICAL``

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: import ppl
            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~8,~0,~7)(~6,~1,~5)(~4,~2,~3)", "RRBRRBRRB")
            sage: cs = ppl.Constraint_System()
            sage: x = [ppl.Variable(e) for e in range(vt.num_edges())]
            sage: vt._set_subspace_constraints(cs.insert, x)
            sage: for g in cs:
            ....:     print(vector(ZZ, g.coefficients()))
            (1, -1, 1, 0, 0, 0, 0, 0, 0)
            (1, 0, 0, 0, 0, 0, 0, -1, 1)
            (0, 1, 0, 0, 0, -1, -1, 0, 0)
            (0, 0, 1, 1, -1, 0, 0, 0, 0)
            (0, 0, 0, 1, -1, 1, 0, 0, 0)
            (0, 0, 0, 0, 0, 0, 1, -1, 1)
        """
        for (i, j, k) in self.degenerate_triangles(slope):
            # i is degenerate
            insert(x[i // 2] == 0)
            insert(x[j // 2] == x[k // 2])

        for (i, j, k) in self.non_degenerate_triangles(slope):
            # i is large
            insert(x[i // 2] == x[j // 2] + x[k // 2])

    def _set_subspace_constraints_fast(self, cs, L, slope, shift):
        zero = L.base_ring().zero()
        one = L.base_ring().one()
        m_one = -one
        for (i, j, k) in self.degenerate_triangles(slope):
            # is is degenerate
            cs.insert(LinearConstraint(op_EQ, L.element_class(L, {shift + i // 2: one}, zero)), check=False)
            cs.insert(LinearConstraint(op_EQ, L.element_class(L, {shift + j // 2: one, k // 2: m_one}, zero)), check=False)

        for (i, j, k) in self.non_degenerate_triangles(slope):
            # is is large
            cs.insert(LinearConstraint(op_EQ, L.element_class(L, {shift + i // 2: one, shift + j // 2: m_one, shift + k // 2: m_one}, zero)), check=False)

    @staticmethod
    def _constraint_check(x, error=AssertionError):
        if not x:
            raise error("does not satisfy train-track constraints")

    def train_track_switch_constraints(self, slope=VERTICAL):
        r"""
        Return the linear constraints of the train-track.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: fp = "(0,3,8)(~0,5,6)(~3,4,2)(~4,1,7)"
            sage: cols = "BBBRRRRRR"
            sage: vt = VeeringTriangulation(fp, cols)
            sage: cs = vt.train_track_switch_constraints()
            sage: cs
            {-1*x0 - x3 + x8 == 0, -1*x0 - x5 + x6 == 0, -1*x1 + x4 - x7 == 0, -1*x2 - x3 + x4 == 0}
        """
        from sage.rings.integer_ring import ZZ
        from .polyhedron.linear_expression import LinearExpressions
        ne = self.num_edges()
        L = LinearExpressions(ZZ)
        cs = ConstraintSystem(ne)
        variables = [L.variable(e) for e in range(ne)]
        self._set_subspace_constraints(cs.insert, variables, slope)
        return cs

    def _set_train_track_constraints(self, insert, x, slope, low_bound, allow_degenerations):
        r"""
        Sets the equations and inequations for train tracks.

        INPUT:

        - ``insert`` - a function to be called for each equation or inequation

        - ``x`` - variable factory (the variable for edge ``e`` is constructed
          via ``x[e]``)

        - ``slope`` - the slope of the train-track ``HORIZONTAL`` or ``VERTICAL``

        - ``low_bound`` - boolean - whether to set lower bounds to 0 or 1

        - ``allow_degenerations`` - boolean - allow to ignore the lower bound
          in appropriate situations

        EXAMPLES::

            sage: from veerer import *

            sage: T  = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])

            sage: l = []
            sage: x = [SR.var("x0"), SR.var("x1"), SR.var("x2")]
            sage: T._set_train_track_constraints(l.append, x, HORIZONTAL, 0, False)
            sage: l
            [x0 == x1 + x2, x0 == x1 + x2, x0 >= 0, x1 >= 0, x2 >= 0]

            sage: l = []
            sage: x = [SR.var("x0"), SR.var("x1"), SR.var("x2")]
            sage: T._set_train_track_constraints(l.append, x, HORIZONTAL, 1, False)
            sage: l
            [x0 == x1 + x2, x0 == x1 + x2, x0 >= 1, x1 >= 1, x2 >= 1]

            sage: l = []
            sage: x = [SR.var("x0"), SR.var("x1"), SR.var("x2")]
            sage: T._set_train_track_constraints(l.append, x, HORIZONTAL, 3, False)
            sage: l
            [x0 == x1 + x2, x0 == x1 + x2, x0 >= 3, x1 >= 3, x2 >= 3]

            sage: l = []
            sage: x = [SR.var("x0"), SR.var("x1"), SR.var("x2")]
            sage: T._set_train_track_constraints(l.append, x, HORIZONTAL, 2, True)
            sage: l
            [x0 == x1 + x2, x0 == x1 + x2, x0 >= 2, x1 >= 0, x2 >= 2]

        This can also be used to check that a given vector satisfies the train-track
        equations::

            sage: T._set_train_track_constraints(T._constraint_check, [2,1,1], HORIZONTAL, False, False)
            sage: T._set_train_track_constraints(T._constraint_check, [1,1,1], HORIZONTAL, False, False)
            Traceback (most recent call last):
            ...
            AssertionError: does not satisfy train-track constraints

        Check equations with folded edges (that are "counted twice")::

            sage: T = VeeringTriangulation("(0,2,3)(~0,1,4)(~1,5,6)", [BLUE, RED, RED, BLUE, BLUE, BLUE, BLUE])
            sage: T._set_train_track_constraints(T._constraint_check, [0,1,1,1,1,1,0], VERTICAL, False, False)
            sage: T._set_train_track_constraints(T._constraint_check, [1,2,3,4,3,7,5], VERTICAL, False, False)
        """
        if slope == VERTICAL:
            POS = BLUE
            NEG = RED
            ZERO = GREEN
        elif slope == HORIZONTAL:
            POS = RED
            NEG = BLUE
            ZERO = PURPLE
        else:
            raise ValueError('bad slope parameter')

        low_bound = max(0, int(low_bound))
        ne = self.num_edges()
        ep = self._ep

        # switch
        self._set_subspace_constraints(insert, x, slope)

        # non-negativity
        for e in range(ne):
            if self._colouring[e] == ZERO:
                # already done in switch conditions: insert(x[e] == 0)
                pass
            elif not low_bound or \
                (allow_degenerations and \
                 ((slope == HORIZONTAL and self.is_forward_flippable(e, check=False)) or \
                 (slope == VERTICAL and self.is_backward_flippable(e, check=False)))):
                insert(x[e] >= 0)
            else:
                insert(x[e] >= low_bound)

    def _set_delaunay_constraints_fast(self, cs, L):
        zero = L.base_ring().zero()
        one = L.base_ring().one()
        minus_one = -one
        ne = self.num_edges()
        for e in self.forward_flippable_edges():
            a, _, _, d = self.square_about_half_edge(2 * e, check=False)
            a = a // 2
            d = d // 2
            # y[a] + y[d] - x[e] >= 0
            l = L.element_class(L, {ne + a: one, ne + d: one, e: minus_one}, zero)
            cs.insert(LinearConstraint(op_GE, l), check=False)
        for e in self.backward_flippable_edges():
            a, _, _, d = self.square_about_half_edge(2 * e, check=False)
            a = a // 2
            d = d // 2
            # x[a] + x[d] - y[e] >= 0
            l = L.element_class(L, {a: one, d: one, ne + e: minus_one}, zero)
            cs.insert(LinearConstraint(op_GE, l), check=False)

    def _set_delaunay_constraints(self, insert, x, y, hw_bound=0):
        r"""
        Set the geometric constraints.

        INPUT:

        - ``insert`` - function

        - ``x``, ``y`` - variables

        - ``hw_bound`` - a nonegative number

        EXAMPLES::

            sage: from veerer import *

            sage: T  = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [RED, RED, BLUE])

            sage: l = []
            sage: x = [SR.var("x0"), SR.var("x1"), SR.var("x2")]
            sage: y = [SR.var("y0"), SR.var("y1"), SR.var("y2")]
            sage: T._set_delaunay_constraints(l.append, x, y)
            sage: l
            [x1 <= y0 + y2, y0 <= x1 + x2]
        """
        hw_bound = max(0, int(hw_bound))
        for e in self.forward_flippable_edges():
            a, _, _, d = self.square_about_half_edge(2 * e, check=False)
            a //= 2
            d //= 2
            insert(x[e] <= y[a] + y[d] - hw_bound)
        for e in self.backward_flippable_edges():
            a, _, _, d = self.square_about_half_edge(2 * e, check=False)
            a //= 2
            d //= 2
            insert(y[e] <= x[a] + x[d] - hw_bound)

    def _set_balance_constraints(self, insert, x, slope, homogeneous):
        r"""
        Linear constraints for the balanced polytope.
        """
        if homogeneous:
            if slope == VERTICAL:
                for eff, ebf in itertools.product(self.forward_flippable_edges(), self.backward_flippable_edges()):
                    a, b, c, d = self.square_about_half_edge(2 * ebf, check=False)
                    insert(x[b // 2] + x[c // 2] >= x[eff])
            elif slope == HORIZONTAL:
                for eff, ebf in itertools.product(self.forward_flippable_edges(), self.backward_flippable_edges()):
                    a, b, c, d = self.square_about_half_edge(2 * eff, check=False)
                    insert(x[b // 2] + x[c // 2] >= x[ebf])
            else:
                raise ValueError("slope must be HORIZONTAL or VERTICAL")
        else:
            if slope == VERTICAL:
                for e in self.forward_flippable_edges():
                    insert(x[e] <= 1)
                for e in self.backward_flippable_edges():
                    a, b, c, d = self.square_about_half_edge(2 * e, check=False)
                    insert(x[b // 2] + x[c // 2] >= 1)
            elif slope == HORIZONTAL:
                for e in self.forward_flippable_edges():
                    a, b, c, d = self.square_about_half_edge(2 * e, check=False)
                    insert(x[b // 2] + x[c // 2] >= 1)
                for e in self.backward_flippable_edges():
                    insert(x[e] <= 1)
            else:
                raise ValueError("slope must be HORIZONTAL or VERTICAL")

    def train_track_linear_space(self, slope=VERTICAL, backend=None):
        r"""
        Deprecated method

        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation("(0,1,2)(~2,~0,~1)", "RRB")
            sage: T.train_track_linear_space().lines()
            doctest:warning
            ...
            UserWarning: train_track_linear_space is deprecated; use generators_matrix() instead
            [[1, 1, 0], [1, 0, -1]]
            sage: T.generators_matrix().rows()
            [(1, 1, 0), (-1, 0, 1)]

            sage: T.train_track_linear_space(HORIZONTAL).lines()
            [[1, 1, 0], [1, 0, 1]]
            sage: T.generators_matrix(HORIZONTAL).rows()
            [(-1, -1, 0), (-1, 0, -1)]
        """
        from warnings import warn
        warn('train_track_linear_space is deprecated; use generators_matrix() instead')

        ne = self.num_edges()
        L = LinearExpressions(ZZ)
        cs = ConstraintSystem(ne)
        x = [L.variable(e) for e in range(ne)]
        self._set_subspace_constraints(cs.insert, x, slope)
        return cs.cone(backend)

    def train_track_polytope(self, slope=VERTICAL, low_bound=0, backend=None):
        r"""
        Deprecated method.
        """
        if low_bound:
            raise NotImplementedError

        from warnings import warn
        warn('train_track_polytope is deprecated; use cone instead')
        return self.cone(slope=slope, backend=backend)

    def cone_min(self, slope=VERTICAL, allow_degenerations=False):
        r"""
        Return the minimal integral point satisfying the constraints.

        INPUT:

        - ``slope`` - the slope of the cone constraints

        - ``allow_degenerations`` - boolean - if ``True`` then allow certain
          degenerations to occur.

        OUTPUT: a point from ppl

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2),(-1,-2,-3)], [RED, RED, BLUE])
            sage: T.cone_min(VERTICAL)
            (1, 2, 1)
            sage: T.cone_min(VERTICAL, True)
            (0, 1, 1)

            sage: T.cone_min(HORIZONTAL)
            (2, 1, 1)
            sage: T.cone_min(HORIZONTAL, True)
            (1, 0, 1)
        """
        R = self.base_ring()
        if R is not ZZ and R is not QQ:
            raise NotImplementedError

        ne = self.num_edges()
        M = ppl.MIP_Problem(ne)

        x = [ppl.Variable(e) for e in range(ne)]
        M.set_objective_function(-sum(x))
        self._set_subspace_constraints(M.add_constraint, x, slope)
        if allow_degenerations:
            M.add_constraint(sum(x[e] for e in range(ne)) >= 1)
            for e in range(ne):
                M.add_constraint(x[e] >= 0)
        else:
            for e in range(ne):
                M.add_constraint(x[e] >= 1)
        return vector(R, M.optimizing_point().coefficients())

    def train_track_min_solution(self, *args, **kwds):
        r"""
        Deprecated method.

        TESTS::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2),(-1,-2,-3)], [RED, RED, BLUE])
            sage: T.train_track_min_solution(VERTICAL)
            doctest:warning
            ...
            UserWarning: train_track_min_solution is deprecated; use cone_min instead
            (1, 2, 1)
            sage: T.train_track_min_solution(VERTICAL, allow_degenerations=True)
            (0, 1, 1)

            sage: T.train_track_min_solution(HORIZONTAL)
            (2, 1, 1)
            sage: T.train_track_min_solution(HORIZONTAL, allow_degenerations=True)
            (1, 0, 1)
        """
        from warnings import warn
        warn('train_track_min_solution is deprecated; use cone_min instead')
        return self.cone_min(*args, **kwds)

    def cone(self, slope=VERTICAL, backend=None):
        r"""
        Return the cone of coordinates for the given ``slope``.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation([(0,1,2),(-1,-2,-3)], [RED, RED, BLUE])
            sage: P = T.cone(VERTICAL)
            sage: P
            Cone of dimension 2 in ambient dimension 3 made of 2 facets (backend=ppl)
            sage: sorted(P.rays())
            [[0, 1, 1], [1, 1, 0]]

            sage: P = T.cone(VERTICAL, low_bound=3)  # not tested
            sage: P.generators()  # not tested
            Generator_System {ray(1, 1, 0), ray(0, 1, 1), point(3/1, 6/1, 3/1)}

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [GREEN, RED, BLUE])
            sage: sorted(T.cone(VERTICAL).rays())
            [[0, 1, 1]]
            sage: sorted(T.cone(HORIZONTAL).rays())
            [[1, 0, 1], [1, 1, 0]]

            sage: T = VeeringTriangulation([(0,1,2), (-1,-2,-3)], [PURPLE, BLUE, RED])
            sage: sorted(T.cone(VERTICAL).rays())
            [[1, 0, 1], [1, 1, 0]]
            sage: sorted(T.cone(HORIZONTAL).rays())
            [[0, 1, 1]]

        One can also use other backends::

            sage: sorted(T.cone(VERTICAL, backend='sage').rays())
            [[1, 0, 1], [1, 1, 0]]
            sage: sorted(T.cone(HORIZONTAL, backend='sage').rays())
            [[0, 1, 1]]

        Examples with boundaries (meromorphic differentials)::

            sage: VeeringTriangulation("", "(0:1)(~0:1)", "R").cone()
            Cone of dimension 1 in ambient dimension 1 made of 1 facets (backend=ppl)
            sage: VeeringTriangulation("(0,1,2)(~1,~2,3)", "(~0:1)(~3:1)", "RBRR").cone()
            Cone of dimension 2 in ambient dimension 4 made of 2 facets (backend=ppl)

        Linear families::

            sage: vt, s, t = VeeringTriangulations.L_shaped_surface(1, 3, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(vt, [s, t])
            sage: f.cone(VERTICAL)
            Cone of dimension 2 in ambient dimension 7 made of 2 facets (backend=ppl)
            sage: f.cone(HORIZONTAL)
            Cone of dimension 2 in ambient dimension 7 made of 2 facets (backend=ppl)

            sage: sorted(f.cone(VERTICAL).rays())
            [[0, 1, 3, 3, 1, 1, 0], [1, 0, 0, 1, 1, 1, 1]]
            sage: sorted(f.cone(HORIZONTAL).rays())
            [[1, 0, 0, 1, 1, 1, 1], [3, 1, 3, 0, 2, 2, 3]]
        """
        R = self.base_ring()
        L = LinearExpressions(R)
        zero = R.zero()
        one = R.one()
        ne = self.num_edges()
        cs = ConstraintSystem(ne)

        # non-negativity
        for e in range(ne):
            cs.insert(LinearConstraint(op_GE, L.element_class(L, {e : one}, zero)), check=False)

        self._set_subspace_constraints_fast(cs, L, slope, 0)
        return cs.cone(backend)

    def delaunay_cone(self, x_low_bound=0, y_low_bound=0, hw_bound=0, backend=None):
        r"""
        Return the geometric polytope of this veering triangulation.

        The geometric polytope is the polytope of length and heights data that
        corresponds to L-infinity Delaunay triangulations.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: T.delaunay_cone()
            4-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB") made of
             1 forward-flip facets
             1 backward-flip facets
             2 x-degeneration facets
             2 y-degeneration facets
            sage: T.delaunay_cone(x_low_bound=1, y_low_bound=1, hw_bound=1)  # not tested

            sage: T.delaunay_cone(backend='sage')
            4-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB") made of
             1 forward-flip facets
             1 backward-flip facets
             2 x-degeneration facets
             2 y-degeneration facets

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: T.delaunay_cone()
            4-dimensional Delaunay cone of VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB") made of
             1 forward-flip facets
             1 backward-flip facets
             2 x-degeneration facets
             2 y-degeneration facets
            sage: T.as_linear_family().delaunay_cone(backend='ppl')
            4-dimensional Delaunay cone of VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]) made of
             1 forward-flip facets
             1 backward-flip facets
             2 x-degeneration facets
             2 y-degeneration facets
            sage: T.as_linear_family().delaunay_cone(backend='sage')
            4-dimensional Delaunay cone of VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]) made of
             1 forward-flip facets
             1 backward-flip facets
             2 x-degeneration facets
             2 y-degeneration facets

        An example in genus 2 involving a linear constraint::

            sage: vt, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(vt, [s, t])
            sage: PG = f.delaunay_cone(backend='ppl')
            sage: PG
            4-dimensional Delaunay cone of VeeringTriangulationLinearFamily("(0,2,3)(~0,1,4)(~1,5,6)", "BRRBBBB", [(1, 0, 0, 1, 1, 1, 1), (0, 1, 1, 1, 1, 1, 0)]) made of
             1 forward-flip facets
             1 backward-flip facets
             2 x-degeneration facets
             2 y-degeneration facets
            sage: sorted(PG.rays())
            [(0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1),
             (0, 1, 1, 1, 1, 1, 0, 2, 0, 0, 2, 2, 2, 2),
             (0, 1, 1, 1, 1, 1, 0, 2, 2, 2, 0, 0, 0, 2),
             (0, 2, 2, 2, 2, 2, 0, 1, 1, 1, 0, 0, 0, 1),
             (1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1),
             (1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1),
             (2, 0, 0, 2, 2, 2, 2, 1, 1, 1, 0, 0, 0, 1)]
        """
        if x_low_bound or y_low_bound or hw_bound:
            raise NotImplementedError

        try:
            return self._delaunay_cone[backend]
        except (AttributeError, KeyError):
            pass

        R = self.base_ring()
        L = LinearExpressions(R)
        zero = R.zero()
        one = R.one()
        ne = self.num_edges()
        cs = ConstraintSystem(2 * ne)

        # non-negativity
        for i in range(2 * ne):
            cs.insert(LinearConstraint(op_GE, L.element_class(L, {i : one}, zero)), check=False)

        self._set_delaunay_constraints_fast(cs, L)
        self._set_subspace_constraints_fast(cs, L, VERTICAL, 0)
        self._set_subspace_constraints_fast(cs, L, HORIZONTAL, ne)
        from .delaunay_cone import DelaunayCone
        delaunay_cone = DelaunayCone(self.copy(mutable=False), cs.cone(backend))
        if not self._mutable:
            try:
                cache = self._delaunay_cone
            except AttributeError:
                cache = self._delaunay_cone = {}
            self._delaunay_cone[backend] = delaunay_cone
        return delaunay_cone

    def geometric_polytope(self, *args, **kwds):
        from warnings import warn
        warn('geometric_polytope is deprecated; use delaunay_cone instead')
        return self.delaunay_cone(*args, **kwds)

    def linear_subvariety(self):
        r"""
        Return the linear subvariety generated by this family.

        Note that if the family is not prime, its decomposition into prime
        components is computed.
        """
        from .linear_subvariety import IrreducibleRealLinearSubvariety
        DS = [component.delaunay_strebel_automaton()._graph for atom, component in self.prime_decomposition()]
        return IrreducibleRealLinearSubvariety(DS)

    def delaunay_automaton(self, run=True, backward=None, backend=None):
        r"""
        Return the Delaunay automaton containing this veering triangulation or family.

        INPUT:

        - ``run`` -- optional boolean (default ``True``) -- whether to run the exploration
          of the automaton

        - ``backward`` -- optional boolean -- whether to run the search both forward and
          backward. By default, it is turn to ``False`` for holomorphic differentials and
          to ``True`` for meromorphic differentials.

        - ``backend`` -- an optional string -- a choice of backend for cone computations.
          A reasonable default choice is made based upon your installation and the base
          ring of the family.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: fp = "(0,~7,6)(1,~8,~2)(2,~6,~3)(3,5,~4)(4,8,~5)(7,~1,~0)"
            sage: cols = "RBRBRBBBB"
            sage: vt = VeeringTriangulation(fp, cols)
            sage: vt.delaunay_automaton()
            Delaunay automaton with 54 states

        Meromorphic example (with a non strongly connected automaton)::

            sage: fp = "(0,2,1)(~0,3,~1)"
            sage: bdry = "(~2:2,~3:2)"
            sage: cols = "RBRR"
            sage: vt = VeeringTriangulation(fp, bdry, cols)
            sage: vt.delaunay_automaton()
            Delaunay automaton with 3 states
            sage: vt.delaunay_automaton(backward=False)
            Delaunay automaton with 1 state
        """
        from .automaton import DelaunayAutomaton
        if backward is None:
            backward = any(self._bdry)
        A = DelaunayAutomaton(backward=backward, backend=backend)
        A.add_seed(self)
        if run:
            A.run()
        return A

    def geometric_automaton(self, *args, **kwds):
        r"""
        Deprecated method.
        """
        from warnings import warn
        warn('geometric_automaton is deprecated; use delaunay_automaton instead')
        return self.delaunay_automaton(self, *args, **kwds)

    def delaunay_strebel_automaton(self, run=True, backward=None, verbosity=0, backend=None):
        r"""
        Return the Delaunay-Strebel automaton containing this veering triangulation.

        INPUT:

        - ``run`` -- optional boolean (default ``True``) -- whether to run the exploration
          of the automaton

        - ``backward`` -- optional boolean -- whether to run the search both forward and
          backward. By default, it is turn to ``False`` for holomorphic differentials and
          to ``True`` for meromorphic differentials.

        - ``backend`` -- an optional string -- a choice of backend for cone computations.
          A reasonable default choice is made based upon your installation and the base
          ring of the family.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: fp = "(0,2,1)(~0,3,~1)"
            sage: bdry = "(~2:2,~3:2)"
            sage: cols = "RBRR"
            sage: vt = VeeringTriangulation(fp, bdry, cols)
            sage: vt.delaunay_strebel_automaton()
            Delaunay-Strebel automaton with 10 states
        """
        from .automaton import DelaunayStrebelAutomaton
        if backward is None:
            backward = any(self._bdry)
        A = DelaunayStrebelAutomaton(backward=backward, verbosity=verbosity, backend=backend)
        A.add_seed(self)
        if run:
            A.run()
        return A

    def delaunay_strebel_graph(self):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,2,1)(~0,3,~1)(~2:2,~3:2)", "RBRR")
            sage: vt.delaunay_strebel_graph()
            Delaunay-Strebel graph of VeeringTriangulation("(0:1,1:1,~0:1,~1:1)", "RB") made of
              9 veering Delaunay states
              1 Strebel states
              8 flip transitions
              5 rotation transitions
              5 Strebel transitions
        """
        from .delaunay_strebel_graph import DelaunayStrebelGraph
        return DelaunayStrebelGraph(self.delaunay_strebel_automaton()._graph)

    def _complexify_generators(self, Gx):
        r"""
        Given ``Gx`` a matrix whose rows are admissible lengths return the
        corresponding admissible heights.

        EXAMPLES::

            sage: from veerer import *

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: Gx = matrix(QQ, 2, [s, t])
            sage: Gy = T._complexify_generators(Gx)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(0), VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(1), VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gy.row(0), HORIZONTAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gy.row(1), HORIZONTAL)

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(2, 3, 4, 5, 1, 2)
            sage: Gx = matrix(QQ, 2, [s, t])
            sage: Gy = T._complexify_generators(Gx)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(0), VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gx.row(1), VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gy.row(0), HORIZONTAL)
            sage: T._set_subspace_constraints(T._constraint_check, Gy.row(1), HORIZONTAL)
        """
        if Gx.ncols() != self._ne:
            raise ValueError
        Gy = Gx.__copy__()
        for j in range(self._ne):
            if self._colouring[j] == BLUE:
                for i in range(Gy.nrows()):
                    Gy[i, j] *= -1
        return Gy

    def _complexify_equations(self, Lx):
        r"""
        Given ``Lx`` a matrix whose right kernel is some subspace of
        admissible lengths, return the admissible heights.

        EXAMPLES::

            sage: from veerer import *

            sage: V = VectorSpace(QQ, 7)

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: Gx = matrix(QQ, 2, [s, t])
            sage: Gy = T._complexify_generators(Gx)
            sage: Lx = Gx.right_kernel_matrix()
            sage: V1 = V.subspace(T._complexify_equations(Lx))
            sage: V2 = V.subspace(Gy.right_kernel_matrix())
            sage: assert V1 == V2

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(2, 3, 4, 5, 1, 2)
            sage: Gx = matrix(QQ, 2, [s, t])
            sage: Gy = T._complexify_generators(Gx)
            sage: Lx = Gx.right_kernel_matrix()
            sage: V1 = V.subspace(T._complexify_equations(Lx))
            sage: V2 = V.subspace(Gy.right_kernel_matrix())
            sage: assert V1 == V2
        """
        if Lx.ncols() != self._ne:
            raise ValueError
        Ly = Lx.__copy__()
        for j in range(self._ne):
            if self._colouring[j] == BLUE:
                for i in range(Ly.nrows()):
                    Ly[i, j] *= -1
        return Ly

    def flat_structure(self, x, y, mutable=False, check=True):
        r"""
        Return a flat structure from two coordinates ``x`` and ``y``.
        """
        if check:
            self._set_train_track_constraints(self._constraint_check, x, VERTICAL, False, False)
            self._set_train_track_constraints(self._constraint_check, y, HORIZONTAL, False, False)

        from .flat_structure import FlatVeeringTriangulation
        return FlatVeeringTriangulation(self, x, y, mutable=mutable, check=check)

    def flat_structure_middle(self, backend=None):
        r"""
        Return a flat structure with this Veering triangulation.

        Note that this triangulation must be core. The point is chosen
        by taking the interior point of the polytope obtained by
        summing each ray.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation("(0,1,2)", "RRB")
            sage: T.flat_structure_middle()
            FlatVeeringTriangulation("(0,1,2)", "RRB", (1, 2, 1), (2, 1, 1))

            sage: x = polygen(QQ)
            sage: K = NumberField(x^2 - x - 1, 'c0', embedding=(1+AA(5).sqrt())/2)
            sage: c0 = K.gen()
            sage: T = VeeringTriangulation("(0,1,2)(3,4,~0)(5,6,~1)(7,8,~2)(9,~3,10)(11,~8,~4)(12,13,~5)(14,15,~6)(16,~11,~10)(17,18,~12)(19,20,~13)(~20,~15,~18)(~19,~16,~17)(~14,~7,~9)", "BRRRRRBRBBBRBRRRRRBBR")
            sage: deformations = [(1, 0, 1, 0, 1, c0, c0, 0, -1, -c0, -c0, 0, c0, 0, c0, 2*c0, c0, 0, c0, -c0, c0),
            ....:                 (0, 1, 1, 0, 0, c0, c0 - 1, 0, -1, -1, -1, -1, 1, c0 - 1, 1, c0, 0, -c0 + 1, -c0 + 2, -c0 + 1, 2*c0 - 2),
            ....:                 (0, 0, 0, 1, 1, 0, 0, 0, 0, -c0, -c0 + 1, 1, 0, 0, c0, c0, c0, c0 - 1, c0 - 1, -1, 1),
            ....:                 (0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, c0 - 1, c0 - 1, c0 - 1, -c0 + 1)]
            sage: F = VeeringTriangulationLinearFamily(T, deformations)
            sage: F.flat_structure_middle()
            FlatVeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)(~2,7,8)(~3,10,9)(~4,11,~8)(~5,12,13)(~6,14,15)(~7,~9,~14)(~10,16,~11)(~12,17,18)(~13,19,20)(~15,~18,~20)(~16,~17,~19)", ...)

            sage: from surface_dynamics import *              # optional - surface_dynamics
            sage: Q = Stratum({1:4, -1:4}, 2)                 # optional - surface_dynamics
            sage: CT = VeeringTriangulation.from_stratum(Q)   # optional - surface_dynamics
            sage: CT.flat_structure_middle()                  # optional - surface_dynamics
            FlatVeeringTriangulation("(0,18,~17)(~0,19,~18)...(~7,~23,8)", ... 5, 4, 3, 2, 1))

        TESTS::

            sage: from veerer import *
            sage: t = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBPBRBPRB")
        """
        n = self.num_edges()

        PH = self.cone(HORIZONTAL, backend=backend)
        PV = self.cone(VERTICAL, backend=backend)

        # pick sum of rays
        VH = PH.rays()
        VH = [sum(v[i] for v in VH) for i in range(n)]
        VV = PV.rays()
        VV = [sum(v[i] for v in VV) for i in range(n)]

        return self.flat_structure(VV, VH)

    def flat_structure_min(self, allow_degenerations=False):
        r"""
        Return a flat structure with this Veering triangulation.

        Note that this triangulation must be core. The point is chosen
        by taking the minimum integral point in the cone.

        EXAMPLES::

            sage: from veerer import *

            sage: from surface_dynamics import *             # optional - surface_dynamics
            sage: Q = Stratum({1:4, -1:4}, 2)                # optional - surface_dynamics
            sage: CT = VeeringTriangulation.from_stratum(Q)  # optional - surface_dynamics
            sage: CT.flat_structure_min()                    # optional - surface_dynamics
            FlatVeeringTriangulation("(0,18,~17)(~0,19,~18)...(~7,~23,8)", ... 5, 4, 3, 2, 1))

        By allowing degenerations you can get a simpler solution but
        with some of the edges horizontal or vertical::

            sage: F = CT.flat_structure_min(True)                 # optional - surface_dynamics
            sage: F                                               # optional - surface_dynamics
            FlatVeeringTriangulation("(0,18,~17)(~0,19,~18)...(~7,~23,8)", ... 7, 4, 3, 2, 1, 0))
            sage: F.constellation()                               # optional - surface_dynamics
            VeeringTriangulation("(0,18,~17)(~0,19,~18)...(~7,~23,8)", "RRRRRRRRBBBBBBBBBBBBBBBB")
        """
        x = self.cone_min(VERTICAL, allow_degenerations=allow_degenerations)
        y = self.cone_min(HORIZONTAL, allow_degenerations=allow_degenerations)
        return self.flat_structure(x, y)

    # TODO: examples
    def flat_structure_cylinder(self):
        r"""
        Return a flat structure which makes all topological cylinders flat.

        EXAMPLES::

            sage: from veerer import *
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BBRRRBBRR")
            sage: vt.flat_structure_cylinder()
            FlatVeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BBRRRBBRR", (3, 1, 2, 2, 3, 1, 1, 1, 2), (1, 3, 2, 2, 1, 1, 1, 2, 1))
        """
        ne = self.num_edges()
        M = ppl.MIP_Problem(2 * ne)

        x = [ppl.Variable(e) for e in range(ne)]
        y = [ppl.Variable(ne + e) for e in range(ne)]
        # TODO: add linear subvariety constraints
        self._set_subspace_constraints(M.add_constraint, x, VERTICAL)
        self._set_subspace_constraints(M.add_constraint, y, HORIZONTAL)
        self._set_train_track_constraints(M.add_constraint, x, VERTICAL, 1, False)
        self._set_train_track_constraints(M.add_constraint, y, HORIZONTAL, 1, False)
        for col in [BLUE, RED]:
            for mid, lbdry, rbdry, folded in self.cylinders(col):
                for h in lbdry + rbdry:
                    M.add_constraint(x[h // 2] == y[h // 2])

        xy = [Rational(c) for c in M.optimizing_point().coefficients()]
        return self.flat_structure(xy[:ne], xy[ne:])

    def flat_structure_geometric_middle(self, backend=None):
        r"""
        Return a geometric flat structure obtained by averaging the
        vertices of the geometric polytope.

        EXAMPLES::

            sage: from veerer import *

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
            sage: T.flat_structure_geometric_middle()
            FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", (4, 9, 5), (9, 4, 5))
        """
        ne = self.num_edges()
        r = self.delaunay_cone(backend=backend).rays()
        VV = [sum(v[i] for v in r) for i in range(ne)]
        VH = [sum(v[ne + i] for v in r) for i in range(ne)]

        return self.flat_structure(VV, VH)

    def zippered_rectangles(self, x, y, base_ring=None, check=True):
        r"""
        Return the zippered rectangle surface associated to the holonomy data ``x`` and ``y``.

        This construction only works for Abelian differentials.

        For each wedge with an upward separatrix we consider a horizontal
        segment based at the bottom of the wedge as wide as the triangle. Then
        we consider downward vertical separatrices and extend them until they
        touch the union of these horizontal segments.

        INPUT:

        - ``x``, ``y`` -- list of positive numbers (as many as edges in this veering
          triangulation)

        - ``base_ring`` -- an optional base ring to build the surface

        - ``check`` -- optional boolean (default ``True``)

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, BLUE, RED

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBB")
            sage: x = [1, 2, 1]
            sage: y = [1, 1, 2]
            sage: vt.zippered_rectangles(x, y)  # optional: sage_flatsurf
            Translation Surface in H_1(0^3) built from a square and a rectangle

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,4)(~2,5,3)(~3,~4,~5)", "RBBRBR")
            sage: x = [1,2,1,2,1,1]
            sage: y = [1,1,2,1,2,3]
            sage: vt.zippered_rectangles(x, y)  # optional: sage_flatsurf
            Translation Surface in H_1(0^7) built from 3 squares and a rectangle

            sage: vt = VeeringTriangulation("(0,~2,1)(2,~8,~3)(3,~7,~4)(4,6,~5)(5,8,~6)(7,~1,~0)", "PRBPRBPBR")
            sage: R0, R1 = vt.dehn_twists(RED)
            sage: B0, B1 = vt.dehn_twists(BLUE)
            sage: f = B0 **2 * R0 **3 * B1 * R1 ** 5
            sage: a, x, y = f.self_similar_widths_and_heights()
            sage: S = vt.zippered_rectangles(x, y)  # optional: sage_flatsurf
            sage: S  # optional: sage_flatsurf
            Translation Surface in H_2(2, 0^9) built from 6 rectangles

        We now check that labelling of the rectangles in ``S`` coincide with
        the order of faces in the veering triangulation::

            sage: from veerer import HORIZONTAL
            sage: for i, r in enumerate(vt.right_wedges(HORIZONTAL)):  # optional: sage_flatsurf
            ....:     e0, e1, e2, e3 = S.polygon(i).erase_marked_vertices().edges()
            ....:     w = e0[0]
            ....:     h = e1[1]
            ....:     l = vt.previous_in_face(r)
            ....:     nr = vt._norm(r)
            ....:     nl = vt._norm(l)
            ....:     assert (w == x[nr] and h == y[nl]) or (w == x[nl] and h == y[nr])

        TESTS::

            sage: from veerer import VeeringTriangulation, BLUE, RED
            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBB")
            sage: x = [1, 2, 1]
            sage: y = [1, 1, 2]
            sage: vt.zippered_rectangles(x, y, base_ring=AA)  # optional: sage_flatsurf
            Translation Surface in H_1(0^3) built from a square and a rectangle
        """
        ans, edge_orientations = self.is_abelian(certificate=True)
        if not ans:
            raise ValueError('the construction is only valid for Abelian differentials')

        if check:
            if len(x) != self._ne or len(y) != self._ne:
                raise ValueError("x and y must have the same length as the number of edges (got {} and {} instead of {})".format(len(x), len(y), self._ne))
            if base_ring is None:
                from sage.structure.sequence import Sequence
                base_ring = Sequence(list(x) + list(y)).universe()
        elif base_ring is None:
            base_ring = self.base_ring()

        colouring = self.colouring_from_xy(x, y, check=False)
        for col0, col1 in zip(colouring, self._colouring):
            if col1 == GREEN or col1 == PURPLE:
                continue
            if col0 != col1:
                raise ValueError('invalid monodromy data')

        ep = self._ep

        # Each separatrix is in between two consecutive edges of
        # distinct colours around a vertex
        # We label separatrices as follows
        #
        #            4i+2
        #             ^
        #             |
        #             |
        #           c2|c1
        # 4i+3  <-----x----> 4i+1
        #             |c0
        #             |
        #             |
        #             v
        #             4i

        # compute for each half-edge the label of the next separatrix
        left_wedges = []
        right_wedges = []
        next_separatrix = [-1] * (2 * self._ne)
        previous_separatrix = [-1] * (2 * self._ne)
        i = 0
        for vertex in self.vertices():
            # find a blue half-edge after a down separatrix, that is
            # consecutive a, b at a vertex such that
            # edge_orientations[a] == False and edge_orientations[b] == True
            a = vertex[0]
            b = vertex[1]
            cola = colouring[a // 2]
            colb = colouring[b // 2]
            while not edge_orientations[a] or edge_orientations[b]:
                a = b
                b = self.next_at_vertex(a)
            cola = colouring[a // 2]
            colb = colouring[b // 2]
            assert cola == RED and colb == BLUE, (a, cola, colb)
            while previous_separatrix[b] == -1:
                if i % 2 == 0:
                    assert cola == RED and colb == BLUE, (i, a, cola, b, colb)
                else:
                    assert cola == BLUE and colb == RED, (i, a, cola, b, colb)

                right_wedges.append(a)
                left_wedges.append(b)
                a = b
                b = self.next_at_vertex(a)
                previous_separatrix[a] = i
                next_separatrix[a] = i + 1
                cola = colouring[a // 2]
                colb = colouring[b // 2]
                while cola == colb:
                    previous_separatrix[b] = i
                    next_separatrix[b] = i + 1
                    a = b
                    b = self.next_at_vertex(a)
                    cola = colouring[a // 2]
                    colb = colouring[b // 2]
                # colour change
                i += 1

            # correct the last quadrant
            cola = colouring[a // 2]
            colb = colouring[b // 2]
            assert cola == RED and colb == BLUE
            j = previous_separatrix[b]
            while cola == RED:
                next_separatrix[a] = j
                a = self.previous_at_vertex(a)
                cola = colouring[a // 2]

            # check that we did a multiple of 2pi
            assert i % 4 == 0

        assert all(x != -1 for x in next_separatrix)
        assert all(x != -1 for x in previous_separatrix)
        assert len(right_wedges) == len(left_wedges) == 2 * self.num_faces()
        assert all(colouring[right_wedges[i] // 2] == RED for i in range(0, 2 * self.num_faces(), 2))
        assert all(colouring[right_wedges[i] // 2] == BLUE for i in range(1, 2 * self.num_faces(), 2))
        assert all(colouring[left_wedges[i] // 2] == BLUE for i in range(0, 2 * self.num_faces(), 2))
        assert all(colouring[left_wedges[i] // 2] == RED for i in range(1, 2 * self.num_faces(), 2))

        # In order to have a consistent labelling between the triangles as provided by self.faces()
        # and the rectangles we compute the face index associated to each half-edge and use it
        # later to order the rectangles
        half_edge_face_index = [-1] * (2 * self._ne)
        for i, face in enumerate(self.faces()):
            for e in face:
                half_edge_face_index[e] = i

        # There are as many rectangles in the Markov partitions as triangles in
        # the veering triangulation
        # Each left/right/bottom separatrix has a certain number of cut points
        # (on both sides)
        rectangles = [None] * self.num_faces()
        for i in range(1, 2 * self.num_faces(), 2):
            l = left_wedges[i]
            L = ep(l)
            r = right_wedges[i]
            R = ep(r)
            e = self.next_in_face(r)
            E = ep(e)
            assert self.next_in_face(e) == L

            # The rectangles are always built starting from the bottom left corner
            # as in the following picture
            #
            #   o----------------o
            #   |  p5         p4 |
            #   |p6            p3|
            #   |                |
            #   |p7            p2|
            #   | p0          p1 |
            #   o----------------o
            if i % 4 == 1:
                # right rectangle
                # bottom side
                p0 = (next_separatrix[R], RIGHT, x[r // 2])
                if x[l // 2] < x[r // 2]:
                    # small case: x[l] = x[r] - x[e]
                    p1 = (next_separatrix[R], RIGHT, x[e // 2])
                else:
                    # big case: x[l] = x[r] + x[e]
                    p1 = (previous_separatrix[e], LEFT, x[e // 2])
                # right side
                p2 = (next_separatrix[L], RIGHT, y[e // 2])
                p3 = (next_separatrix[L], RIGHT, y[l // 2])
                # top side
                p4 = (next_separatrix[r], RIGHT, x[l // 2])
                p5 = (next_separatrix[r], RIGHT, 0)
                # left side
                p6 = (previous_separatrix[r], LEFT, 0)
                p7 = (previous_separatrix[r], LEFT, y[r // 2])

            else:
                # bottom side
                if x[r // 2] < x[l // 2]:
                    # small case: x[r] = x[l] - x[e]
                    p0 = (previous_separatrix[L], LEFT, x[e // 2])
                else:
                    # big case: x[r] = x[l] + x[e]
                    p0 = (next_separatrix[E], RIGHT, x[e // 2])
                p1 = (previous_separatrix[L], LEFT, x[l // 2])
                # right side
                p2 = (next_separatrix[l], RIGHT, y[l // 2])
                p3 = (next_separatrix[l], RIGHT, 0)
                # top side
                p4 = (next_separatrix[r], LEFT, 0)
                p5 = (next_separatrix[r], LEFT, x[r // 2])
                # left side
                p6 = (previous_separatrix[R], LEFT, y[r // 2])
                p7 = (previous_separatrix[R], LEFT, y[e // 2])

            j = half_edge_face_index[r]
            rectangles[j] = (p0, p1, p2, p3, p4, p5, p6, p7)

        from .tatami_decomposition import tatami_decomposition
        return tatami_decomposition(rectangles, base_ring)

    def is_core(self, backend=None):
        r"""
        Test whether this coloured triangulation is core.

        It is core if both the vertical and horizontal train track polytopes
        contain positive vectors.

        EXAMPLES::

            sage: from veerer import *

            sage: triangles = [(-24, -2, -23), (-22, 2, 22), (-21, 3, 21), (-20, 4, 20),
            ....:              (-19, 1, 19), (-18, 6, 18), (-17, 7, 17), (-16, 16, -1),
            ....:              (-15, -8, -14), (-13, 13, -7), (-12, 12, -6), (-11, 11, -5),
            ....:              (-10, -4, 8), (-9, -3, 23), (0, 15, 14), (5, 10, 9)]
            sage: colours = [RED, RED, RED, RED, RED, RED, RED, RED, BLUE, BLUE, BLUE,
            ....:            BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE, BLUE,
            ....:            BLUE, BLUE, BLUE]

            sage: T = VeeringTriangulation(triangles, colours)
            sage: T.is_core()
            True

            sage: U = T.copy(mutable=True)
            sage: U.flip(10, BLUE)
            sage: U.is_core()
            True

            sage: U = T.copy(mutable=True)
            sage: U.flip(10, RED)
            sage: U.is_core()
            False

        Examples involving linear subspaces::

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,~2)", [RED, RED, BLUE])
            sage: vt.as_linear_family().is_core()
            True
            sage: VeeringTriangulationLinearFamily(vt, [1, 0, -1]).is_core()
            False

        A torus with boundaries in the stratum H_1(2, -2)::

            sage: t = Triangulation("(0,2,1)(3,~1,~0)", boundary="(~3:2,~2:2)")
            sage: VeeringTriangulation(t, colouring="RRBB").is_core()
            True
            sage: VeeringTriangulation(t, colouring="BRBR").is_core()
            False
            sage: VeeringTriangulation(t, colouring="RBRB").is_core()
            False
        """
        if any(c == PURPLE or c == GREEN for c in self._colouring):
            raise ValueError('core not implemented with PURPLE or GREEN colour')

        # TODO: could use v.has_curve for every edge?
        # In theory LP should be much faster but in practice (in small dimensions)
        # polytope is much better
        d = self.dimension()
        return self.cone(VERTICAL, backend=backend).affine_dimension() == d and \
               self.cone(HORIZONTAL, backend=backend).affine_dimension() == d

    def is_delaunay(self, backend=None):
        r"""
        Test whether this coloured triangulation is geometric.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: vt1 = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBBBRBBRB")
            sage: vt2 = VeeringTriangulation("(0,~8,~3)(1,6,~2)(2,~1,~0)(3,7,~4)(4,8,~5)(5,~7,~6)", "RBBBRBRBB")
            sage: vt1.is_delaunay()
            True
            sage: vt2.is_delaunay()
            False

        An example in genus 2 involving a linear subspace::

            sage: from veerer import VeeringTriangulations, VeeringTriangulationLinearFamily
            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(T, [s, t])
            sage: f.is_delaunay()
            True
        """
        dim = self.dimension()
        P = self.delaunay_cone(backend=backend)
        Pdim = P.affine_dimension()
        assert Pdim <= 2 * dim
        return Pdim == 2 * dim

    # TODO: deprecate
    def is_geometric(self, *args, **kwds):
        r"""
        Deprecated method.

        TESTS::

            sage: from veerer import VeeringTriangulation

            sage: vt1 = VeeringTriangulation("(0,~6,~3)(1,7,~2)(2,~1,~0)(3,5,~4)(4,8,~5)(6,~8,~7)", "RBBBRBBRB")
            sage: vt1.is_geometric()
            doctest:warning
            ...
            UserWarning: is_geometric is deprecated; use is_delaunay instead
            True
        """
        from warnings import warn
        warn('is_geometric is deprecated; use is_delaunay instead')
        return self.is_delaunay(*args, **kwds)

    def balanced_polytope(self, slope=VERTICAL, homogeneous=False, backend=None):
        r"""
        Return the set of balanced coordinates for this veering triangulation<<

        INPUT:

        - ``slope`` - either ``VERTICAL`` (default) or ``HORIZONTAL``

        - ``homogeneous`` - boolean. Default to ``False``.
        """
        from sage.rings.rational_field import QQ
        ne = self.num_edges()
        cs = ConstraintSystem()
        L = LinearExpressions(QQ)
        x = [L.variable(e) for e in range(ne)]
        self._set_train_track_constraints(cs.insert, x, slope, False, False)
        self._set_balance_constraints(cs.insert, x, slope, homogeneous)
        return cs.polyhedron(backend)

    def is_balanced(self, slope=VERTICAL, backend=None):
        r"""
        Check balanceness

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBR")
            sage: T.is_balanced()  # not tested
            True

            sage: T = VeeringTriangulation("(0,~3,2)(1,4,~2)(3,5,~4)(~5,~1,~0)", "RBBBRB")
            sage: T.is_balanced()  # not tested
            False

            sage: T = VeeringTriangulation("(0,1,8)(2,~7,~1)(3,~0,~2)(4,~5,~3)(5,6,~4)(7,~8,~6)", "BRRRRBRBR", mutable=True)
            sage: T.is_balanced()  # not tested
            False
            sage: T.rotate()
            sage: T.is_balanced()  # not tested
            True
        """
        return self.balanced_polytope(backend=backend).affine_dimension() == self.dimension()

    def edge_has_curve(self, e, check=True, verbose=False):
        r"""
        Return whether there is a curve which crosses ``e`` in the associated
        (dual) train-track.

        EXAMPLES::

            sage: from veerer import *

            sage: t = [(-6, -4, -5), (-3, -1, 3), (-2, 0, 4), (1, 5, 2)]
            sage: c = [RED, RED, BLUE, RED, BLUE, RED]
            sage: T0 = VeeringTriangulation(t, c)
            sage: T0.is_core()
            True

        Flipping edge 3 in RED is fine (it remains a core triangulation)::

            sage: T1 = T0.copy(mutable=True)
            sage: T1.flip(3, RED)
            sage: T1.edge_has_curve(3)
            True
            sage: T1.is_core()
            True

        However, flipping edge 3 in BLUE leads to a non-core triangulation::

            sage: T2 = T0.copy(mutable=True)
            sage: T2.flip(3, BLUE)
            sage: T2.edge_has_curve(3)
            False
            sage: T2.is_core()
            False

        Equivalently, the cone is degenerate::

            sage: P1 = T1.cone(VERTICAL)
            sage: P1.affine_dimension()
            3
            sage: P2 = T2.cone(VERTICAL)
            sage: P2.affine_dimension()
            2
        """
        if check:
            e = self._check_edge(e)

        # TODO: we should only search for vertex cycles; i.e. not allow more
        # than two pairs (i, ~i) to be both seen (barbell are fine but not more)

        # TODO: we want the ._colouring to also take care of negative edges
        # (bad alternative: take "norm" function from flipper)
        colouring = self._colouring
        edge_rep = self._edge_rep
        ep = self._ep

        if verbose:
            print('[edge_has_curve] checking edge %s with colour %s' % (edge_rep(e), colouring[e]))

        a, b, c, d = self.square_about_half_edge(2 * e, check=False)
        cola = colouring[a // 2]
        colb = colouring[b // 2]
        colc = colouring[c // 2]
        cold = colouring[d // 2]
        cole = colouring[e]
        if cola == BLUE or colb == RED:
            assert colc == BLUE or cold == RED
            POS, NEG = BLUE, RED
            if verbose:
                print('[edge_has_curve] checking HORIZONTAL track')
        else:
            assert cola == RED or colb == BLUE
            assert colc == RED or cold == BLUE
            POS, NEG = RED, BLUE
            if verbose:
                print('[edge_has_curve] checking VERTICAL track')

        # check alternating condition
        assert cole == BLUE or colouring[e] == RED
        assert cola != colb
        assert colc != cold

        if cole == NEG:
            start = b
            end = ep(d)
            if verbose:
                print('[edge_has_curve] try to find path from b=%s to ~d=%s' %
                         (edge_rep(start), edge_rep(end)))
        else:
            start = a
            end = ep(c)
            if verbose:
                print('[edge_has_curve] try to find path from a=%s to ~c=%s' %
                         (edge_rep(start), edge_rep(end)))

        if start == end:
            return True

        n = 2 * self._ne
        fp = self._fp
        seen = [False] * n
        seen[start] = True
        q = collections.deque()
        q.append(start)
        while q:
            f = q.popleft()
            if verbose:
                print('[edge_has_curve] crossing %s' % edge_rep(f))

            # here we set r and s so that the triangle is (r, s, ~f)
            r = fp[ep(f)]
            s = fp[r]
            if verbose:
                print('[edge_has_curve] switch with r=%s s=%s' % (edge_rep(r), edge_rep(s)))
            if not seen[r] and not (colouring[r // 2] == POS and colouring[ep(f) // 2] == NEG):
                if r == end:
                    if verbose:
                        print('[edge_has_curve] done at %s' % edge_rep(r))
                    return True
                seen[r] = True
                q.append(r)
                if verbose:
                    print('[edge_has_curve] adding %s on top of the queue' % edge_rep(r))
            if not seen[s] and not (colouring[s // 2] == NEG and colouring[ep(f) // 2] == POS):
                if s == end:
                    if verbose:
                        print('[edge_has_curve] done at %s' % edge_rep(s))
                    return True
                seen[s] = True
                q.append(s)
                if verbose:
                    print('[edge_has_curve] adding %s on top of the queue' % edge_rep(s))

        return False

    def delaunay_flips(self, backend=None):
        r"""
        Return the list of Delaunay flips.

        A flip, a rather a list of flips, is geometric if it arises generically
        as a flip of L^oo-Delaunay triangulations along Teichmueller geodesics.
        Each geometric flip corresponds to a facet of the geometric polytope.

        OUTPUT: a list of pairs ``(edge_number, new_colour)``

        EXAMPLES::

            sage: from veerer import *

            sage: vt = VeeringTriangulation("(0,2,3)(1,4,~0)(5,6,~1)", "BRRBBBB")
            sage: sorted(vt.delaunay_flips())
            [([3], 1), ([3], 2), ([4], 1), ([4], 2), ([5], 1), ([5], 2)]
            sage: sorted(vt.delaunay_flips(backend='sage'))
            [([3], 1), ([3], 2), ([4], 1), ([4], 2), ([5], 1), ([5], 2)]

        L-shaped square tiled surface with 3 squares (given as a sphere with
        3 triangles). It has two geometric neighbors corresponding to simultaneous
        flipping of the diagonals 3, 4 and 5::

            sage: from veerer import *
            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(T, [s, t])
            sage: sorted(f.delaunay_flips(backend='ppl'))
            [([3, 4, 5], 1), ([3, 4, 5], 2)]
            sage: sorted(f.delaunay_flips(backend='sage'))
            [([3, 4, 5], 1), ([3, 4, 5], 2)]
            sage: sorted(f.delaunay_flips(backend='normaliz-QQ'))  # optional - pynormaliz
            [([3, 4, 5], 1), ([3, 4, 5], 2)]

        To be compared with the geometric flips in the ambient stratum::

            sage: sorted(T.delaunay_flips())
            [([3], 1), ([3], 2), ([4], 1), ([4], 2), ([5], 1), ([5], 2)]
            sage: sorted(T.as_linear_family().delaunay_flips())
            [([3], 1), ([3], 2), ([4], 1), ([4], 2), ([5], 1), ([5], 2)]

        A more complicated example in which edge 4 have a forced colour after
        flip and where the flippable edges 0 and 3 are not part of any geometric
        flips::

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(2, 3, 5, 2, 1, 1)
            sage: f = VeeringTriangulationLinearFamily(T, [s, t])
            sage: T.flippable_edges()
            [0, 3, 4, 5, 6]
            sage: sorted(f.delaunay_flips(backend='ppl'))
            [([4], 2), ([5], 1), ([5], 2)]
            sage: sorted(f.delaunay_flips(backend='sage'))
            [([4], 2), ([5], 1), ([5], 2)]
            sage: sorted(f.delaunay_flips(backend='normaliz-QQ'))  # optional - pynormaliz
            [([4], 2), ([5], 1), ([5], 2)]

        TESTS::

            sage: from veerer import VeeringTriangulation
            sage: fp = "(0,~8,~7)(1,3,~2)(2,7,~3)(4,6,~5)(5,8,~6)(~4,~1,~0)"
            sage: cols = "RBRRRRBBR"
            sage: vt = VeeringTriangulation(fp, cols)
            sage: sorted(vt.delaunay_flips())
            [([2], 1), ([2], 2), ([4, 8], 1), ([4, 8], 2)]
            sage: sorted(vt.as_linear_family().delaunay_flips())
            [([2], 1), ([2], 2), ([4, 8], 1), ([4, 8], 2)]
        """
        ne = self._ne
        delaunay_cone = self.delaunay_cone()
        rays = delaunay_cone.rays()
        ans = []
        for facet, edges in delaunay_cone.forward_delaunay_facets():
            e = edges[0]
            a, b, c, d = self.square_about_half_edge(2 * e)
            a //= 2
            b //= 2
            c //= 2
            d //= 2
            colours = 0
            # TODO: here we do not need to run through all rays. It is actually
            # sufficient to run through a basis of the support of the facet.
            for i in facet.ambient_V_indices():
                r = rays[i]
                if r[ne + b] > r[ne + a]:
                    assert self._colouring[e] == RED
                elif r[ne + b] < r[ne + a]:
                    assert self._colouring[e] == BLUE
                if r[a] < r[d]:
                    colours |= RED
                    if colours & BLUE:
                        break
                if r[a] > r[d]:
                    colours |= BLUE
                    if colours & RED:
                        break
            assert colours
            if colours & RED:
                ans.append((edges, RED))
            if colours & BLUE:
                ans.append((edges, BLUE))
        return ans

    def geometric_flips(self, *args, **kwds):
        import warnings
        warnings.warn('the method geometric_flips is deprecated; use delaunay_flips instead')

        return self.delaunay_flips(*args, **kwds)

    # TODO: this is mostly a copy/past with variation of the forward version
    # above. The code would better be factorized
    def backward_delaunay_flips(self, backend=None):
        r"""
        Return the list of backward Delaunay flips.

        A flip, a rather a list of flips, is geometric if it arises generically
        as a flip of L^oo-Delaunay triangulations along Teichmueller geodesics.
        Each geometric flip corresponds to a facet of the geometric polytope.

        OUTPUT: a list of pairs ``(edge_number, new_colour)``

        EXAMPLES::

            sage: from veerer import *

        An example with meromorphic differentials in H(2, -2)::

            sage: fp = "(0,2,1)(~0,3,~1)"
            sage: bdry = "(~2:2,~3:2)"
            sage: cols0 = "BRRR"
            sage: cols1 = "BBRR"
            sage: cols2 = "RBRR"
            sage: VeeringTriangulation(fp, bdry, cols0).backward_delaunay_flips()
            []
            sage: sorted(VeeringTriangulation(fp, bdry, cols1).backward_delaunay_flips())
            [([0], 1), ([0], 2)]
            sage: sorted(VeeringTriangulation(fp, bdry, cols2).backward_delaunay_flips())
            [([0], 1), ([0], 2)]

        An example in H_0(1, 0, -1^3)::

            sage: from veerer import VeeringTriangulation
            sage: vt =  VeeringTriangulation("(1,~5,~2)(2,~4,~3)(4,~1,~0)", boundary="(0:1)(3:1)(5:1)", colouring="BRBRBB")
            sage: assert vt.is_delaunay()
            sage: for edges, col in vt.backward_delaunay_flips():
            ....:     vt2 = vt.copy(mutable=True)
            ....:     for e in edges:
            ....:         vt2.flip_back(e, col)
            ....:         assert vt2.is_delaunay()
        """
        ne = self._ne
        delaunay_cone = self.delaunay_cone()
        rays = delaunay_cone.rays()
        ans = []
        for facet, edges in delaunay_cone.backward_delaunay_facets():
            e = edges[0]
            a, b, c, d = self.square_about_half_edge(2 * e)
            a //= 2
            b //= 2
            c //= 2
            d //= 2
            colours = 0
            for i in facet.ambient_V_indices():
                r = rays[i]
                if r[a] > r[b]:
                    assert self._colouring[e] == RED
                if r[a] < r[b]:
                    assert self._colouring[e] == BLUE
                if r[ne + a] > r[ne + d]:
                    colours |= RED
                    if colours & BLUE:
                        break
                if r[ne + a] < r[ne + d]:
                    colours |= BLUE
                    if colours & RED:
                        break
            assert colours
            if colours & RED:
                ans.append((edges, RED))
            if colours & BLUE:
                ans.append((edges, BLUE))
        return ans

    def random_forward_flip_sequence(self, length=1, relabel=False):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,2,3)(1,4,~0)(5,6,~1)", "BRRBBBB")
            sage: vt.random_forward_flip_sequence(5) # random
            VeeringFlipSequence(VeeringTriangulation("(0,2,3)(~0,1,4)(~1,5,6)", "BRRBBBB"), "3B 4B 5B 6B 0R", "()")
            sage: vt.random_forward_flip_sequence(5, relabel=True) # random
            VeeringFlipSequence(VeeringTriangulation("(0,2,3)(~0,1,4)(~1,5,6)", "BRRBBBB"), "4B 5B 3R 2B 0B", "(0,~1)(~0,1)(2,6,3,5,4)(~2,~6,~3,~5,~4)")
        """
        V = self.copy(mutable=True)
        cols = [RED, BLUE]
        flips = []
        for _ in range(length):
            e = choice(V.forward_flippable_edges())
            col = choice(cols)

            # TODO: this is a bit annoying. There should be a method to
            # test what are the valid colouring
            V.flip(e, col, reduced=False)
            if not V.edge_has_curve(e):
                col = BLUE if col == RED else RED
            V.flip_back(e, PURPLE)
            V.flip(e, col)
            flips.append((e, col))

        if relabel:
            relabelling = perm_random_centralizer(self.edge_permutation())
        else:
            relabelling = perm_id(2 * self._ne)

        from .flip_sequence import VeeringFlipSequence
        return VeeringFlipSequence(self, flips, relabelling)

    # TODO: this will not work with purple edges
    def random_forward_flip(self, repeat=1):
        r"""
        Apply a forward flip randomly among the ones that keeps the triangulation core.

        INPUT:

        - ``repeat`` - integer (default 1) - if provided make ``repeat`` flips instead of 1.
        """
        if not self._mutable:
            raise ValueError('immutable veering triangulation; use a mutable copy instead')

        cols = [RED, BLUE]
        for _ in range(repeat):
            e = choice(self.forward_flippable_edges())
            old_col = self._colouring[e]
            shuffle(cols)
            for c in cols:
                self.flip(e, c)
                if self.edge_has_curve(e):
                    break
                else:
                    self.flip_back(e, old_col)

    def constraints_matrix(self, slope=VERTICAL):
        r"""
        Return a matrix of constraints on x or y coordinates.
        """
        if slope == VERTICAL:
            LAR = PURPLE
            POS = BLUE
            NEG = RED
            ZERO = GREEN
        elif slope == HORIZONTAL:
            LAR = GREEN
            POS = RED
            NEG = BLUE
            ZERO = PURPLE
        else:
            raise ValueError('bad slope parameter')

        ans = matrix(ZZ, self.num_triangles(), self.num_edges())
        for s, (i,j,k) in enumerate(self.triangles()):
            i //= 2
            ci = self._colouring[i]
            j //= 2
            cj = self._colouring[j]
            k //= 2
            ck = self._colouring[k]

            if ci == ZERO and cj == NEG and ck == POS:
                # i is degenerate
                raise NotImplementedError
            elif cj == ZERO and ck == NEG and ci == POS:
                # j is degenerate
                raise NotImplementedError
            elif ck == ZERO and ci == NEG and cj == POS:
                # k is degenerate
                raise NotImplementedError
            elif ck == LAR or (ci == POS and cj == NEG):
                # k is large
                ans[s, k] += 1
                ans[s, i] -= 1
                ans[s, j] -= 1
            elif ci == LAR or (cj == POS and ck == NEG):
                # i is large
                ans[s, i] += 1
                ans[s, j] -= 1
                ans[s, k] -= 1
            elif cj == LAR or (ck == POS and ci == NEG):
                # j is large
                ans[s, j] += 1
                ans[s, k] -= 1
                ans[s, i] -= 1
            else:
                raise ValueError('can not determine the nature of triangle (%s, %s, %s) with colors (%s, %s, %s) in %s direction' %
                                 (self._edge_rep(i), self._edge_rep(j), self._edge_rep(k),
                                  colour_to_string(ci), colour_to_string(cj), colour_to_string(ck),
                                  'horizontal' if slope == HORIZONTAL else 'vertical'))

        return ans

    def generators_matrix(self, slope=VERTICAL, mutable=True):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~7,~5)(~3,~4,~2)(~6,~1,~8)", "RRBRRBRRB")
            sage: m = vt.generators_matrix()
            sage: m  # random
            sage: m.echelon_form()
            [ 1  0 -1  0 -1 -1  0  0  0]
            [ 0  1  1  0  1  1  0  1  1]
            [ 0  0  0  1  1  0  0  0  0]
            [ 0  0  0  0  0  0  1  0 -1]
            sage: vt = VeeringTriangulation("", boundary="(0:1,1:1,2:1)(~2:3,~0:1,~1:2)", colouring="RRR")
            sage: m = vt.generators_matrix()  # random
            sage: m  # random
            [1 0 0]
            [0 1 0]
            [0 0 1]
            sage: m.echelon_form()
            [1 0 0]
            [0 1 0]
            [0 0 1]
        """
        subspace = self.constraints_matrix(slope).right_kernel_matrix()
        if not mutable:
            return subspace
        return subspace.__copy__()

    def parallel_cylinders(self, col=RED):
        r"""
        Return the L-parallel cylinders.

        The output is a list of lists ``[l0, l1, ...]`` where each ``li``
        represents a L-parallel family of cylinders, together with circumference.

        EXAMPLES::

            sage: from veerer.linear_family import VeeringTriangulationLinearFamilies
            sage: X9 = VeeringTriangulationLinearFamilies.prototype_H1_1(0, 2, 1, -1)
            sage: X9.parallel_cylinders()
            [([([14, 9, 7, 16], [4], [2, 0], True), ([10, 12], [], [1], True)], [1, 1])]
        """
        cylinders = list(self.cylinders(col))
        if not cylinders:
            []

        C = []  # middle edges
        for cyl in cylinders:
            c = [0] * self.num_edges()  # indicatrix of the middle edges
            for e in cyl[0]:
                c[e // 2] = 1
            C.append(c)

        # take intersection of the cylinder twists in the tangent space
        F = FreeModule(self.base_ring(), self.num_edges())
        U = F.submodule(self.generators_matrix())
        T = F.submodule(C)

        # what would be even nicer are the equations on the coefficients of C
        basis = U.intersection(T).basis_matrix()
        twist_coeffs = []
        C = matrix(C)
        seen = set()
        parallel_families = []
        for b in basis.rows():
            # conjecture: the reduced echelon form is a basis with the following property
            # * the nonzero positions for elements of the basis are disjoint (correspond to a weighted union of cylinders)
            # * it is >= 0
            # In other words, the equivalence classes of Benirschke are tight by a single equation.
            # Moreover, the coefficients give the circumference ratios
            u = C.solve_left(b)
            u = vector_normalize(self.base_ring(), u)
            pos = u.nonzero_positions()
            assert not any(i in seen for i in pos)
            seen.update(pos)
            parallel_cylinders = [cylinders[i] for i in pos]
            parallel_families.append((parallel_cylinders, [u[i] for i in pos]))

        return parallel_families

    # TODO: change edges_low/edges_up to low_edges/up_edges
    def degeneration(self, edges_low=None, edges_up=None, mutable=False, collapsed_half_edge_relabelling=False, check=True):
        r"""
        Return the veering triangulation obtained by blowing-up the given subset of ``edges``.

        This corresponds to a a two levels degeneration in the BCGGM compactification.

        The output is a 4-tuple ``(f_up, f_low, relabelling_up, relabelling_low)`` where
        - ``f_up`` and ``f_low`` are ``VeeringTriangulationLinearFamily``s
        - ``relabelling_up``, ``relabelling_low`` are partial maps from the half-edges of this
          veering triangulation to the half-edges in respectively ``f_up`` and ``f_low``

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily

        Horizontal degeneration (cylinder blowup)::

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~2,~3,~7)(~1,~8,~6)(~5,~0,~4)", "RBRRBBRBR")
            sage: f_up, f_low, r_up, r_low = vt.degeneration(edges_low=[0, 1, 2, 3, 4, 5, 7], edges_up=[6, 8])
            sage: f_up is None
            True
            sage: f_low.stratum()  # optional - surface_dynamics
            H_1(2, -1^2)

            sage: f_up, f_low, r_up, r_low = vt.degeneration(edges_low=[0, 1, 2, 3, 6, 7, 8], edges_up=[4, 5])
            sage: f_up is None
            True
            sage: f_low.stratum()  # optional - surface_dynamics
            H_1(2, -1^2)

            sage: f_up, f_low, r_up, r_low = vt.degeneration(edges_low=[0, 1, 2, 3, 7], edges_up=[4, 5, 6, 8])
            sage: f_up is None
            True
            sage: f_low.stratum()  # optional - surface_dynamics
            H_0(2, -1^4)
            sage: r_low
            array('i', [0, 1, 2, 3, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, 8, 9, -1, -1])

        Note that when we degenerate two cylinders, the residue condition becomes codimension one
        in the associated stratum::

            sage: f_low.dimension() == f_low.stratum().dimension() - 1  # optional - surface_dynamics # not tested
            True
            sage: f_low.residue_constraints().echelon_form()
            [1 0 1 0]
            [0 1 0 1]

        Collapsing the two marked point of a torus in H(0,0)::

            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,~0)(~3,4,5)(~5,~2,~4)", "BRRRRB")
            sage: f_up, f_low, r_up, r_low = vt.degeneration(edges_low=[5], edges_up=[0, 1, 2, 3, 4])
            sage: f_up.stratum()  # optional - surface_dynamics
            H_1(0)
            sage: f_low.stratum()  # optional - surface_dynamics
            H_0(0^2, -2)

        Examples related to parallel cylinder degeneration in the gothic locus::

            sage: vt = VeeringTriangulation("(0,13,~21)(1,3,~2)(2,9,~3)(4,20,~5)(5,~26,~6)(6,~19,~7)(7,~16,~8)(8,~10,~9)(10,15,~11)(11,24,~12)(12,~14,~13)(14,~25,~15)(16,18,~17)(17,26,~18)(19,25,~20)(21,23,~22)(22,~24,~23)(~4,~1,~0)", "RBBRBRBBRBBRBBRBBBRRBBBRBBB")
            sage: _, f_low, _, _ = vt.degeneration(edges_up=[1, 2, 4, 6, 7, 9, 10, 12, 13, 15, 16, 17, 20, 21, 22, 24, 25, 26], mutable=True)
            sage: f_low.set_canonical_labels()

        An example with folded edges::

            sage: vt = VeeringTriangulation("(0,2,7)(1,4,9)(3,12,14)(5,~7,8)(6,~9,~10)(~8,13,~11)(10,~12,11)", "BRBRRBRRBBBBRRB")
            sage: vt.degeneration(edges_low=(14,))
            (VeeringTriangulationLinearFamily("(0,2,6)(1,3,8)(4,~6,7)(5,~8,~9)(~7,12,~10)(9,11,10)", "BRBRBRRBBBBRR", [(1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1), (0, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 0), (0, 0, 1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 1), (0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, -1, 0), (0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -1), (0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1)]),
                 VeeringTriangulationLinearFamily("(0:7)", "B", [(1)]),
                 array('i', [0, -1, 2, -1, 4, -1, -1, -1, 6, -1, 8, -1, 10, -1, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, -1, 22, 24, -1, -1, -1]),
                 array('i', [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, -1]))

            sage: vt.degeneration(edges_low=(0, 2, 6, 7, 14))
            (VeeringTriangulationLinearFamily("(0,1,3)(2,6,~4)(~3,5,4)", "RRBBBRR", [(1, 0, 0, -1, 0, 1, 0), (0, 1, 0, 1, 0, -1, 0), (0, 0, 1, 0, 0, 0, -1), (0, 0, 0, 0, 1, 1, 1)]),
             VeeringTriangulationLinearFamily("(0,1,3)(2:2,4:2,~3:1)", "BBRRB", [(1, 0, 0, 1, 0), (0, 1, 0, -1, 0), (0, 0, 1, 0, 0), (0, 0, 0, 0, 1)]),
             array('i', [-1, -1, 0, -1, -1, -1, -1, -1, 2, -1, -1, -1, -1, -1, -1, -1, -1, 4, 6, -1, 7, -1, 8, 9, -1, 10, 12, -1, -1, -1]),
             array('i', [0, -1, -1, -1, 2, -1, -1, -1, -1, -1, -1, -1, 4, -1, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 8, -1]))

        TESTS:

        These examples used to not work::

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2:2,~3:2)", "BRRR")
            sage: vt.degeneration([0], [1, 2, 3])
            (VeeringTriangulationLinearFamily("(0:2,~0:2)", "R", [(1)]),
             VeeringTriangulationLinearFamily("(0:3)(~0:3)", "B", [(1)]),
             array('i', [-1, -1, -1, -1, -1, 0, -1, 1]),
             array('i', [0, 1, -1, -1, -1, -1, -1, -1]))

            sage: vt = VeeringTriangulation("(0,1,2)(~2,3,4)(~4,5,6)", "BRBRBRB")
            sage: vt.degeneration(edges_low=[1], edges_up=[0, 2, 3, 4, 5, 6])
            (VeeringTriangulationLinearFamily("(0,1,2)(~2,3,4)", "BRBRB", [(1, 0, 1, 0, 1), (0, 1, 1, 0, 1), (0, 0, 0, 1, 1)]),
             VeeringTriangulationLinearFamily("(0:3)", "R", [(1)]),
             array('i', [-1, -1, -1, -1, -1, 0, 2, -1, 4, 5, 6, -1, 8, -1]),
             array('i', [-1, -1, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]))

            sage: vt = VeeringTriangulation("(0,1,2)(~2,3,4)(~4,5,6)", "BRBRBRB")
            sage: vt.degeneration(edges_low=[1, 3, 5], edges_up=[0, 2, 4, 6])
            (None,
             VeeringTriangulationLinearFamily("(0:1,1:1,2:1)(3:1)", "RRRR", [(1, 0, 0, 1), (0, 1, 0, 1), (0, 0, 1, 1)]),
             array('i', [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]),
             array('i', [-1, -1, 0, -1, -1, -1, 2, -1, -1, -1, 4, -1, -1, -1]))

            sage: vt = VeeringTriangulation("(0,1,2)(~2,3,4)(~4,5,6)", "BRBRBRR")
            sage: vt.degeneration(edges_low=[0, 1, 2, 3, 4], edges_up=[5, 6])
            (None,
             VeeringTriangulationLinearFamily("(0,1,2)(~2,3,4)(~4:1)(5:1)", "BRBRBB", [(1, 0, 1, 0, 1, 1), (0, 1, 1, 0, 1, 1), (0, 0, 0, 1, 1, 1)]),
             array('i', [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]),
             array('i', [0, -1, 2, -1, 4, 5, 6, -1, 8, 9, -1, -1, -1, -1]))

            sage: vt = VeeringTriangulation("(0,1,2)(~2,3,4)(~3,5,6)(~6,7,8)", "RBBRRRBBR")
            sage: vt.degeneration(edges_up=[3, 4, 5, 6, 7, 8], edges_low=[0, 1, 2])
            (VeeringTriangulationLinearFamily("(0,~3,4)(1,2,3)", "RRRBB", [(1, 0, 0, 0, -1), (0, 1, 0, -1, -1), (0, 0, 1, 1, 1)]),
             VeeringTriangulationLinearFamily("(0,1,2)(~2:3)", "RBB", [(1, 0, -1), (0, 1, 1)]),
             array('i', [-1, -1, -1, -1, -1, -1, -1, 2, -1, -1, 4, -1, 6, 7, 8, -1, 0, -1]),
             array('i', [0, -1, 2, -1, 4, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]))
            sage: vt.degeneration(edges_up=[3, 4, 5, 6, 7, 8], edges_low=[0, 1, 2], collapsed_half_edge_relabelling=True)
            (VeeringTriangulationLinearFamily("(0,~3,4)(1,2,3)", "RRRBB", [(1, 0, 0, 0, -1), (0, 1, 0, -1, -1), (0, 0, 1, 1, 1)]),
             VeeringTriangulationLinearFamily("(0,1,2)(~2:3)", "RBB", [(1, 0, -1), (0, 1, 1)]),
             array('i', [-1, -1, -1, -1, -1, -1, 2, 2, 3, -1, 4, -1, 6, 7, 8, -1, 0, -1]),
             array('i', [0, -1, 2, -1, 4, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]))
        """
        # We distinguish three kinds of triangles
        # - up triangles: when the three edges are in the up partition
        # - down triangles: when the three edges are in the down partition
        # - mixed triangles: when the triangle has one down edge and two up edges
        n = 2 * self._ne
        m = self._ne
        ep = self._ep
        vp = self._vp
        fp = self._fp
        bdry = self._bdry
        colouring = self._colouring

        if edges_low is None and edges_up is None:
            raise ValueError('must specify at least one of edges_low and edges_up')

        if edges_low is None:
            edges_up = set(edges_up)
            edges_low = set(range(m)).difference(edges_up)
        if edges_up is None:
            edges_low = set(edges_low)
            edges_up = set(range(m)).difference(edges_low)
        else:
            edges_low = set(edges_low)
            edges_up = set(edges_up)

        if check:
            edges_low = set(self._check_edge(e) for e in edges_low)
            edges_up = set(self._check_edge(e) for e in edges_up)
            if not edges_low or not edges_up or edges_low.intersection(edges_up) or edges_low.union(edges_up) != set(range(m)):
                raise ValueError('invalid arguments: edges_low={} edges_up={}'.format(edges_low, edges_up))

        half_edges_up = set(2 * e for e in edges_up).union(2 * e + 1 for e in edges_up if vp[2 * e + 1] != -1)
        half_edges_low = set(2 * e for e in edges_low).union(2 * e + 1 for e in edges_low if vp[2 * e + 1] != -1)

        nt_mix = 0  # number of mixed triangles (ie triangle with two up edges and one low edge)
        n_mix_folded = 0
        mix_p = array('i', [-1] * n)  # involution on mixed edges (crossing triangles)
        for (a, b, c) in self.triangles():
            x = (a in half_edges_up) + (b in half_edges_up) + (c in half_edges_up)
            if x == 1:
                raise ValueError('invalid set of edges: {} is a up-down-down triangle'.format((a, b, c)))
            elif x == 2:
                nt_mix += 1
                if a not in half_edges_up:
                    down = a
                    mix1, mix2 = b, c
                if b not in half_edges_up:
                    down = b
                    mix1, mix2 = c, a
                if c not in half_edges_up:
                    down = c
                    mix1, mix2 = a, b
                if colouring[mix1 // 2] != colouring[mix2 // 2]:
                    raise ValueError('invalid mixed triangle ({}, {}, {}) with colouring ({}, {}, {})'.format(
                        down, mix1, mix2,
                        colour_to_string(colouring[down // 2]),
                        colour_to_string(colouring[mix1 // 2]),
                        colour_to_string(colouring[mix2 // 2])))
                mix_p[mix1] = mix2
                mix_p[mix2] = mix1
                n_mix_folded += (vp[mix1 ^ 1] == -1) + (vp[mix2 ^ 1] == -1)

        n_up = len(half_edges_up) - 2 * nt_mix  # actual number of half-edges in upper level

        # build the upper level (only the face permutation fp_up)
        relabelling_up = array('i', [-1] * n)
        vertical_nodes = []
        n_folded_up = 0
        if n_up:
            # If we only blow-up cylinders (horizontal degenerations) there is no
            # upper level at all
            ne_up = 0
            for a in half_edges_up:
                if mix_p[a] != -1 or relabelling_up[a] != -1:
                    continue

                # build ep
                relabelling_up[a] = 2 * ne_up
                A = ep(a)
                while mix_p[A] != -1:
                    if collapsed_half_edge_relabelling:
                        relabelling_up[A] = 2 * ne_up + 1
                        relabelling_up[mix_p[A]] = 2 * ne_up
                    A = ep(mix_p[A])
                if A != a:
                    relabelling_up[A] = 2 * ne_up + 1
                else:
                    n_folded_up += 1
                ne_up += 1

            assert ne_up <= n_up <= 2 * ne_up

            fp_up = array('i', [-1] * (2 * ne_up))
            angle_excess_up = array('i', [0] * (2 * ne_up))
            colouring_up = array('i', [0] * ne_up)

            for e in half_edges_up:
                if mix_p[e] != -1:
                    continue

                colouring_up[relabelling_up[e] // 2] = colouring[e // 2]

                # Compute the angle excess of the former edge e (named relabelling_up[e]
                # in the upper veering triangulation). We simply apply the formula
                #   new_angle_excess = sum(angle excesses of contracted edges) - length + alternations / 2
                col = colouring[e // 2]
                excess = 0        # excess collected
                alternations = 0  # number of alternations (including start and end)
                length = 0        # number of edges that degenerate along the face
                ee = fp[e]
                while ee not in half_edges_up:
                    excess += bdry[ee]
                    alternations += colouring[ee // 2] != col
                    length += 1
                    col = colouring[ee // 2]
                    ee = fp[ee]
                alternations += colouring[ee // 2] != col
                alternations -= colouring[ee // 2] != colouring[e // 2]  # alternation after degeneration
                excess += bdry[ee]
                fp_up[relabelling_up[e]] = relabelling_up[ee]
                assert alternations % 2 == 0
                angle_excess_up[relabelling_up[ee]] = excess - length + alternations // 2

            vt_up = VeeringTriangulation.from_permutations(None, fp_up, (angle_excess_up,), (colouring_up,), mutable=mutable, check=check)

        else:
            vt_up = None

        # build the lower level
        # In the case of folded cylinder, we need to introduce special edges as
        # circumference of cylinders (in the stratum Q_0(-1^2, -2))
        folded_cylinders = []
        has_cylinder = False
        seen = [False] * 2 * self._ne
        for h in range(0, 2 * self._ne, 2):
            if seen[h] or mix_p[h] == -1:
                continue
            orbit = []
            while not seen[h] and mix_p[h] != -1:
                orbit.append(h)
                seen[h] = True
                h = ep(mix_p[h])
            if mix_p[orbit[-1]] != -1 and ep(mix_p[orbit[-1]]) == orbit[0]:
                has_cylinder = True
                folded = [h for h in orbit if vp[2 * (h // 2) + 1] == -1]
                if len(folded) == 2:
                    assert len(orbit) % 2 == 0
                    i = orbit.index(folded[0])
                    orbit = orbit[i:] + orbit[:i]
                    assert orbit[0] == folded[0]
                    assert orbit[len(orbit) // 2] == folded[1]
                    folded_cylinders.append(orbit)
                else:
                    assert len(folded) == 0

        if vt_up is not None and has_cylinder:
            raise ValueError("mixed horizontal and vertical degeneration")

        relabelling_low = array('i', [-1] * n)
        j = 0
        n_folded_low = 0
        for e in sorted(edges_low):
            relabelling_low[2 * e] = j
            if vp[2 * e + 1] != -1:
                relabelling_low[2 * e + 1] = j + 1
            else:
                n_folded_low += 1
            j += 2

        assert j == len(half_edges_low) + n_folded_low, (j, len(half_edges_low), n_folded_low)
        ne_low = j // 2 + len(folded_cylinders)

        vp_low = array('i', [-1] * (2 * ne_low))
        angle_excess_low = array('i', [0] * (2 * ne_low))
        colouring_low = array('i', [0] * ne_low)
        for e in half_edges_low:
            colouring_low[relabelling_low[e] // 2] = colouring[e // 2]

            excess = bdry[e]
            col = colouring[e // 2]
            alternations = 0
            ee = vp[e]
            while relabelling_low[ee] == -1:
                excess += bdry[ee]
                alternations += colouring[ee // 2] != col
                col = colouring[ee // 2]
                assert col == RED or col == BLUE
                ee = vp[ee]
            vp_low[relabelling_low[e]] = relabelling_low[ee]
            alternations += colouring[ee // 2] != col
            assert (alternations % 2 == 0) == (colouring[e // 2] == colouring[ee // 2])
            angle_excess_low[relabelling_low[e]] = excess + alternations // 2

        # build Q_0(-1^2, -2) components for folded cylinders
        for i, cylinder in enumerate(folded_cylinders):
            j = 2 * (ne_low - i - 1)
            vp_low[j] = j
            angle_excess_low[j] = 1
            col = colouring[cylinder[0] // 2]
            assert all(colouring[h // 2] == col for h in cylinder)
            colouring_low[ne_low - i - 1] = BLUE if col == RED else RED

        vt_low = VeeringTriangulation.from_permutations(vp_low, None, (angle_excess_low,), (colouring_low,), mutable=mutable, check=check)

        edges_up = sorted(edges_up)
        edges_low = sorted(edges_low)

        # compute constraints in order to produce linear families
        constraints = self.constraints_matrix().matrix_from_columns(edges_up + edges_low)
        constraints.echelonize()
        i = 0
        constraints_up = constraints[:, :len(edges_up)]
        while i < constraints_up.nrows() and constraints_up[i]:
            i += 1
        constraints_up = constraints_up[:i]

        constraints_low = constraints[i:, len(edges_up):]
        j = 0
        while j < constraints_low.nrows() and constraints_low[j]:
            j += 1
        constraints_low = constraints_low[:j]

        if folded_cylinders:
            constraints_low_extended = matrix(constraints_low.base_ring(), constraints_low.nrows() + len(folded_cylinders), constraints_low.ncols() + len(folded_cylinders))
            constraints_low_extended[:constraints_low.nrows(), :constraints_low.ncols()] = constraints_low
            for i, cylinder in enumerate(folded_cylinders):
                j = 2 * (ne_low - i - 1)
                col = colouring_low[ne_low - i - 1]
                for h in cylinder:
                    assert colouring[h // 2] != col
                    if colouring[fp[h] // 2] == col:
                        assert fp[h] in half_edges_low
                        constraints_low_extended[constraints_low.nrows() + i, relabelling_low[fp[h]] // 2] += 1
                constraints_low_extended[constraints_low.nrows() + i, ne_low - i - 1] = -1
            constraints_low = constraints_low_extended

        from .linear_family import VeeringTriangulationLinearFamily
        if vt_up is not None:
            generators_up = constraints_up.right_kernel_matrix()
            for e in range(n):
                if mix_p[e] == -1:
                    continue
                a = edges_up.index(e // 2)
                b = edges_up.index(mix_p[e] // 2)
                if generators_up.column(a) != generators_up.column(b):
                    raise RuntimeError('a={} b={}\ngenerators_matrix={}'.format(a, b, generators_up))


            edges_up_to_index = {e: i for i, e in enumerate(edges_up)}
            representatives = [None] * ne_up
            for h, h_up in enumerate(relabelling_up):
                if mix_p[h] != -1 or h_up == -1:
                    # collapsed half edge or edge in lower level
                    continue
                if representatives[h_up // 2] is None:
                    representatives[h_up // 2] = edges_up_to_index[h // 2]

            f_up = VeeringTriangulationLinearFamily(vt_up, generators_up.matrix_from_columns(representatives), mutable=mutable, check=check)
        else:
            # horizontal degeneration
            f_up = None

        f_low = VeeringTriangulationLinearFamily(vt_low, constraints_low.right_kernel_matrix().__copy__(), mutable=mutable, check=check)

        if f_up is not None:
            # some additional checks for vertical degenerations
            assert not self.is_abelian() or (f_up.is_abelian() and f_low.is_abelian())

            angles = self.angles()
            angles_deg = list(f_up.angles()) + list(f_low.angles())

            for a in angles:
                assert a in angles_deg
                del angles_deg[angles_deg.index(a)]
            assert all(a != 0 for a in angles_deg)
            assert sorted(a for a in angles_deg if a > 0) == sorted(-a for a in angles_deg if a < 0)
        else:
            # some additional checks for horizontal degenerations
            assert not self.is_abelian() or f_low.is_abelian()

            angles = self.angles()
            angles_deg = list(f_low.angles())

            for a in angles:
                assert a in angles_deg
                del angles_deg[angles_deg.index(a)]
            assert len(angles_deg) % 2 == 0 and all(a == 0 for a in angles_deg)

        return (f_up, f_low, relabelling_up, relabelling_low)

    def horizontal_degeneration_up_edges_subsets(self):
        for col in [RED, BLUE]:
            for cyl_family, circumference_ratio in self.parallel_cylinders(col):
                edges = set()
                for c, rbdry, lbdry, half in cyl_family:
                    edges.update(i // 2 for i in c)
                yield tuple(sorted(edges))

    def codimension_one_horizontal_degenerations(self, mutable=False, mapping=False, check=True):
        r"""
        Return codimension one horizontal degenerations.

        INPUT:

        - ``mapping`` -- whether to also return the mapping used to relabel edges

        EXAMPLES::

            sage: from veerer import VeeringTriangulation

            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: [degeneration.stratum() for _, degeneration, _, _ in vt.codimension_one_horizontal_degenerations()]  # optional - surface_dynamics
            [H_1(2, -1^2)]

            sage: from veerer.linear_family import VeeringTriangulationLinearFamilies
            sage: X9 = VeeringTriangulationLinearFamilies.prototype_H1_1(0, 2, 1, -1)
            sage: [degeneration.stratum() for _, degeneration, _, _ in vt.codimension_one_horizontal_degenerations()]  # optional - surface_dynamics
            [H_1(2, -1^2)]
        """
        if mapping:
            raise NotImplementedError
        for edges in self.horizontal_degeneration_up_edges_subsets():
            yield self.degeneration(edges_up=edges, mutable=mutable, check=check)

    def vertical_degeneration_low_edges_subsets(self):
        r"""
        Iterate through subsets of admissible edge degenerations of given complex codimension ``codim``.

        Warning: we do not check for the "boundary of cylinder" condition.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily

            sage: vt = VeeringTriangulation("(0,8,~7)(1,3,~2)(2,10,~3)(4,6,~5)(5,11,~6)(7,~9,~8)(9,~11,~10)(~4,~1,~0)", "RRBRBBRRBRRB")
            sage: sorted(vt.vertical_degeneration_low_edges_subsets(), key=lambda x: (len(x), x))
            [(2,), (6,), (8,), (2, 6), (6, 8), (4, 5, 6, 11)]

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0,~7,~5)(~3,~4,~2)(~6,~1,~8)", "RRBRRBRRB")
            sage: sorted(vt.vertical_degeneration_low_edges_subsets(), key=lambda x: (len(x), x))
            [(8,), (2, 3, 4, 5)]

            sage: vt = VeeringTriangulation("(0,~7,6)(1,~5,~2)(2,4,~3)(3,11,~4)(5,10,~6)(7,9,~8)(8,~10,~9)(~11,~1,~0)", "RBRBRRBRBRRR")
            sage: sorted(vt.vertical_degeneration_low_edges_subsets(), key=lambda x: (len(x), x))
            [(1,), (3,), (6,), (8,), (1, 3), (1, 6), (3, 8), (6, 8)]

        TESTS::

        An example which used to be wrong::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~0,3,4)(~1,~3,5)(~2,6,7)(~4,~6,8)(~5,9,10)(~7,11,12)(~8,13,~12)(~9,14,15)(~10,16,17)(~11,18,19)(~13,~14,~16)(~15,20,21)(~17,~18,22)(~19,23,24)(~20,~23,25)(~21,26,~25)(~22,~26,~24)", "RRBBBBRRRRRBRBRBBBRRRBRBRRB")
            sage: sorted(vt.vertical_degeneration_low_edges_subsets(), key=lambda x: (len(x), x))
            [(2,),
             (23,),
             (2, 23),
             (0, 1, 2),
             (20, 23, 25),
             (0, 1, 2, 23),
             (2, 20, 23, 25),
             (0, 1, 2, 3, 4, 5),
             (0, 1, 2, 20, 23, 25),
             (15, 20, 21, 23, 25, 26),
             (0, 1, 2, 3, 4, 5, 23),
             (2, 15, 20, 21, 23, 25, 26),
             (0, 1, 2, 3, 4, 5, 20, 23, 25),
             (0, 1, 2, 15, 20, 21, 23, 25, 26),
             (0, 1, 2, 3, 4, 5, 15, 20, 21, 23, 25, 26),
             (0, 1, 2, 3, 4, 5, 9, 10, 14, 15, 20, 21, 23, 25, 26)]
            sage: for low_edges in vt.vertical_degeneration_low_edges_subsets():
            ....:     fup, flow, _, _ = vt.degeneration(edges_low=low_edges)
            ....:     assert fup is not None and flow is not None
            ....:     assert fup.is_delaunay() and flow.is_delaunay()
        """
        # For each edge e compute the face corresponding to x[e] == 0 and the face to y[e] == 0 (in H-rep)
        delaunay_cone = self.delaunay_cone()
        dim = delaunay_cone.affine_dimension()
        base_ring = self.base_ring()
        ne = self._ne
        space_dim = 2 * ne
        facets = delaunay_cone.facets()
        rays = delaunay_cone.rays()
        CP = delaunay_cone.combinatorial_polyhedron().face_generator()
        vanishing_faces = [delaunay_cone.vanishing_face(e) for e in range(ne)]
        vanishing_H_indices = [frozenset(face.ambient_H_indices()) for face in vanishing_faces]
        facets_kind, facets_data = delaunay_cone.facets_kind_and_data()

        cylinders = collections.defaultdict(set)
        for middle, bot, top, _ in itertools.chain(self.cylinders(RED), self.cylinders(BLUE)):
            # NOTE: each cylinder is a quadruple (middle, bottom, top, folded)
            middle = [h // 2 for h in middle]
            bot = frozenset(h // 2 for h in bot)
            top = frozenset(h // 2 for h in top)
            cylinders[bot].update(top)
            cylinders[bot].update(middle)
            cylinders[top].update(bot)
            cylinders[top].update(middle)

        def complete(face):
            # if x-degenerationn or y-degeneration facets -> complete with its friend
            # if Delaunay -> add x-degeneration and y-degeneration correspond to a,b,c,d
            done = False
            while not done:
                done = True
                ambient_H_indices = set(face.ambient_H_indices())

                # force compl
                for i in list(ambient_H_indices):
                    kind = facets_kind[i]
                    if kind == "x" or kind == "y":
                        # x or y degeneration
                        for e in facets_data[i]:
                            new_indices = vanishing_H_indices[e]
                            if not new_indices.issubset(ambient_H_indices):
                                done = False
                                ambient_H_indices.update(new_indices)
                    elif kind == "f" or kind == "b":
                        # forward or backward Delaunay
                        for e in facets_data[i]:
                            a, b, c, d = self.square_about_half_edge(2 * e)
                            new_indices = set().union(vanishing_H_indices[a // 2], vanishing_H_indices[b // 2], vanishing_H_indices[c // 2], vanishing_H_indices[d // 2])
                        if not new_indices.issubset(ambient_H_indices):
                            done = False
                            ambient_H_indices.update(new_indices)
                if not done:
                    face = CP.meet_of_Hrep(*ambient_H_indices)

            return face

        ans = [set() for _ in range(dim + 1)]
        for e in range(ne):
            e_face = complete(vanishing_faces[e])
            assert e_face.dimension() % 2 == 1  # WARNING: there is a shift in dimension
            codim = dim - (1 + e_face.dimension()) // 2
            ans[codim].add(e_face.ambient_H_indices())

        for codim1 in range(1, dim):
            for Hindices1 in ans[codim1]:
                assert CP.meet_of_Hrep(*Hindices1).dimension() == 2 * dim - 2 * codim1 - 1
                for codim2 in range(1, codim1 + 1):
                    for Hindices2 in ans[codim2]:
                        assert CP.meet_of_Hrep(*Hindices2).dimension() == 2 * dim - 2 * codim2 - 1
                        if Hindices1 != Hindices2:
                            new_face = CP.meet_of_Hrep(*Hindices1, *Hindices2)
                            new_face = complete(new_face)
                            assert new_face.dimension() % 2 == 1
                            codim = dim - (1 + new_face.dimension()) // 2
                            if codim == codim1:
                                assert new_face.ambient_H_indices() == Hindices1, (face.ambient_H_indices(), Hindices1)
                            elif codim == codim2:
                                assert new_face.ambient_H_indices() == Hindices2, (face.ambient_H_indices(), Hindices2)
                            else:
                                assert codim > min(codim1, codim2), (codim, codim1, codim2)
                                ans[codim].add(new_face.ambient_H_indices())

        output = []
        for codim in range(1, dim):
            for Hindices in ans[codim]:
                face = CP.meet_of_Hrep(*Hindices)
                frays = [rays[i] for i in face.ambient_V_indices()]
                vanishing_edges1 = [e for e in range(ne) if all(r[e] == 0 for r in frays)]
                vanishing_edges2 = [e for e in range(ne) if all(r[ne + e] == 0 for r in frays)]
                assert vanishing_edges1 == vanishing_edges2
                output.append(tuple(vanishing_edges1))
        return output

    def codimension_one_vertical_degenerations(self, mutable=False, mapping=False, check=True):
        r"""
        Return codimension one vertical degenerations.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,8,~7)(1,3,~2)(2,10,~3)(4,6,~5)(5,11,~6)(7,~9,~8)(9,~11,~10)(~4,~1,~0)", "RRBRBBRRBRRB")
            sage: [(f_up.stratum(), f_low.stratum()) for (f_up, f_low, _, _) in vt.codimension_one_vertical_degenerations()]  # optional - surface_dynamics
            [(H_2(2), H_0(1^2, -4)),
             (H_2(2), H_0(1^2, -4)),
             (H_2(2), H_0(1^2, -4)),
             (H_1(0^2), H_0(1^2, -2^2)),
             (H_1(0^2), H_0(1^2, -2^2)),
             (H_1(0^2), H_0(1^2, -2^2))]

        TESTS:

        This example used to be wrong::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily
            sage: vt = VeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)(~2,7,8)(~3,~5,9)(~4,10,~8)(~6,11,12)(~7,13,14)(~9,15,16)(~10,~12,17)(~11,18,19)(~13,~15,20)(~14,~16,21)(~17,22,23)(~18,24,~20)(~19,25,26)(~21,~26,~23)(~22,~24,~25)", "BRRRRBRRBRRRBBRRBRBRRRRBRBR")
            sage: subspace = [(1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, -2, 2, 2, 2, 0, -1, 1, 0, 0, 0, 0, 1, 1, 0),
            ....:             (0, 1, 1, 0, 0, 0, 1, 2, 1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 0),
            ....:             (0, 0, 0, 1, 1, 0, 0, -1, -1, 1, 0, 0, 0, -2, 1, 1, 0, 0, -1, 1, -1, 1, 0, 0, 0, 0, 1),
            ....:             (0, 0, 0, 0, 0, 1, -1, 1, 1, -1, 1, 1, 2, 2, -1, -1, 0, -1, 1, 0, 1, -1, 0, 1, 0, 0, 0)]
            sage: f = VeeringTriangulationLinearFamily(vt, subspace)
            sage: assert all(f_up is not None for f_up, _, _, _ in f.codimension_one_vertical_degenerations())
            sage: half_edges = set(f.half_edges())
            sage: for edges_low in sorted(f.vertical_degeneration_low_edges_subsets(), key=lambda x: (len(x), x)):
            ....:     print(edges_low, tuple(sorted(half_edges.difference(edges_low))))
            (0, 16, 25) (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53)
            (5, 12, 23) (0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53)
            (8, 13, 18) (0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53)
            (0, 8, 13, 16, 18, 25) (1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 14, 15, 17, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53)
            sage: for edges_up in f.horizontal_degeneration_up_edges_subsets():
            ....:     print(tuple(sorted(half_edges.difference(edges_up))), edges_up)
            (0, 5, 8, 12, 13, 16, 18, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53) (1, 2, 3, 4, 6, 7, 9, 10, 11, 14, 15, 17, 19, 20, 21, 22, 24, 26)

        Another example that used to be wrong::

            sage: vt = VeeringTriangulation("(0:1,1:1,~0:1,2:1,3:3)(~1:1,4:1,~3:1,~2:3,~4:1)", "BRRRB")
            sage: f_up, f_low, _, _ = vt.degeneration(edges_low=(1,))
            sage: f_up
            VeeringTriangulationLinearFamily("(0:1,~0:2,1:1,2:3)(~1:3,~3:1,3:2,~2:1)", "BRRB", [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)])
            sage: f_low
            VeeringTriangulationLinearFamily("(0:3)(~0:3)", "R", [(1)])
            sage: (f_up.stratum(), f_low.stratum())  # optional - surface_dynamics
            (H_0(2^2, 0^2, -3^2), H_0(2, -2^2))
        """
        for edges in self.vertical_degeneration_low_edges_subsets():
            yield self.degeneration(edges_low=edges, mutable=mutable, check=check)

    def is_half_edge_strebel(self, e, slope=VERTICAL, check=True):
        r"""
        Return whether ``e`` is a Strebel half-edge.

        A half-edge is vertical Strebel (resp. horizontal strebel), if the
        vertical (resp. horizontal) band that is based on this half-edge does
        not hit a conical singularity (ie all trajectories are infinite and
        converge to a common pole).

        EXAMPLES::

            sage: from veerer import *

            sage: vt = VeeringTriangulation("(0,~3,2)(1,3,~2)", boundary="(~1:2,~0:2)", colouring="BBRR")
            sage: for (e0, e1) in vt.edges():
            ....:     print(e0, vt.is_half_edge_strebel(e0), e1, vt.is_half_edge_strebel(e1))
            0 True 1 True
            2 True 3 True
            4 False 5 False
            6 True 7 True
        """
        if check:
            e = self._check_half_edge(e)

        if self._bdry[e]:
            # boundary half-edge
            return True
        else:
            # internal half-edge
            fp = self._fp
            a = fp[e]
            b = fp[a]
            assert e == fp[b]

            ca = self._colouring[a // 2]
            cb = self._colouring[b // 2]

            if slope == VERTICAL:
                return (ca != BLUE or cb != RED)
            elif slope == HORIZONTAL:
                return (ca != RED or cb != BLUE)
            else:
                raise ValueError('invalid slope parameter')

    def strebel_graph(self, slope=VERTICAL, mapping=False, mutable=False):
        r"""
        Return the Strebel graph associated to this veering triangulation.

        INPUT:

        - ``slope`` (optional, default ``VERTICAL``) -- either ``VERTICAL`` or ``HORIZONTAL``

        - ``mutable`` (optional, default ``False``) -- whether the output Strebel graph is mutable

        - ``mapping`` -- whether to return the mapping of edges (the Strebel
          graph is a subgraph of the triangulation) and the mapping of boundary faces (the output list of boundary faces of the Strebel graph corresponds positionally to the list of boundary faces of the input veering triangulation)

        EXAMPLES::

            sage: from veerer import *
            sage: from surface_dynamics import Stratum  # optional - surface_dynamics

        Strebel-veering triangulation in the stratum H(2, -2)::

            sage: t = Triangulation("(0,2,1)(3,~1,~0)", boundary="(~3:2,~2:2)")
            sage: vt = VeeringTriangulation(t, colouring="RBBB")
            sage: sg = vt.strebel_graph(slope=VERTICAL)
            sage: sg
            StrebelGraph("(0,~1:1,~0,1:1)")
            sage: assert sg.stratum() == vt.stratum() == Stratum((2,-2), 1)  # optional - surface_dynamics

            sage: vt = VeeringTriangulation(t, colouring="BRBB")
            sage: sg = vt.strebel_graph(slope=HORIZONTAL)
            sage: sg
            StrebelGraph("(0,~1:1,~0,1:1)")
            sage: assert sg.stratum() == vt.stratum() == Stratum((2,-2), 1)  # optional - surface_dynamics

        More complicated examples::

            sage: triangles = "(0,1,2)(~1,3,4)(~3,5,6)(~6,7,8)"
            sage: boundary = "(~0:1,~2:1,~4:1,~8:1,~7:1,~5:1)"
            sage: colours = "BBRRRRBRB"
            sage: vt = VeeringTriangulation(triangles, boundary, colours)
            sage: sg = vt.strebel_graph()
            sage: sg
            StrebelGraph("(0,1,~1:1,~0,2,~3,4,~4:1,3,~2)")
            sage: assert sg.stratum() == vt.stratum() == Stratum((0, 0, 0, 0, 0, 0, -2), 1)  # optional - surface_dynamics

            sage: boundary = "(~0:2,~2:1,~4:1)(~8:3,~7:1,~5:1)"
            sage: colours = "BBRRRRBRB"
            sage: vt = VeeringTriangulation(triangles, boundary, colours)
            sage: sg = vt.strebel_graph()
            sage: sg
            StrebelGraph("(0:1,1,~1:1,~0,2)(~2,~3:2,4,~4:1,3)")
            sage: assert sg.stratum() == vt.stratum() == Stratum((5, 0, 0, 0, 0, -4, -5), 2) # optional - surface_dynamics
            sage: vt.strebel_graph(mapping=True)
            (StrebelGraph("(0:1,1,~1:1,~0,2)(~2,~3:2,4,~4:1,3)"),
             array('i', [-1, -1, 0, 1, 2, 3, 4, 5, -1, -1, -1, -1, 6, 7, 8, 9, -1, -1]),
             array('i', [1, 9, 1, 5, 9, 11, 11, 17, 17, 15]))

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)", "(~8:2,~7:1,~6:1,~5:2,~4:1,~3:1,~2:2,~1:1,~0:1)", "RBRRBBRRB")
            sage: sg = vt.strebel_graph()
            sage: assert vt.stratum() == sg.stratum() == Stratum((6, 0, 0, 0, 0, -1, -1, -8), 2) # optional - surface_dynamics

            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)", "(~8:1,~7:1,~6:2,~5:1,~4:2,~3:1,~2:2,~1:1,~0:1)", "RBRRBBRRB")
            sage: sg = vt.strebel_graph()
            sage: assert vt.stratum() == sg.stratum() == Stratum((2, 0, 0, 0, 0, 0, 0, -4), 1) # optional - surface_dynamics

        Examples with folded edges::

            sage: VeeringTriangulation("", boundary="(0:1,1:1,2:1,3:1)", colouring="RRRR").strebel_graph()
            StrebelGraph("(0,1,2,3)")
            sage: VeeringTriangulation("(0,1,4)(2,3,5)", boundary="(~5:1,~4:1)", colouring="BRBRBB").strebel_graph()
            StrebelGraph("(0,1,2,3)")

            sage: G = StrebelGraph("(0,1,2)(~0)")
            sage: for cols in G.colourings():
            ....:     for vt in G.veering_triangulations(cols):
            ....:         assert vt.is_strebel() and vt.strebel_graph() == G

        Example where the output mapping of boundary faces differs in order from the list of boundary faces in the output Strebel graph::

            sage: vt = VeeringTriangulation("(1,4,2)(~2,3,~0)(~1:1, ~4:1)(0:1,~3:1)","BRBRB")
            sage: sg = vt.strebel_graph()
            sage: sg.boundary_faces()
            [[0, 1, 2], [3, 4, 5]]
            sage: sg, r1, r2 = vt.strebel_graph(mapping=True)
            sage: sg
            StrebelGraph("(0,~0:1,1)(~1,2,~2:1)")
            sage: r1
            array('i', [-1, -1, 0, 1, 2, 3, 4, 5, -1, -1])
            sage: r2
            array('i', [9, 3, 9, 0, 0, 7])
            sage: assert all(vt.face_angle(r2[h]) == sg.face_angle(h) for h in sg.half_edges())

        TESTS:

        An example with folded edges that used not to work::

            sage: vt = VeeringTriangulation("(0:1)(1:1,2:1,3:1,4:1)(~2:1,~4:1,5:1)(~3:1,~5:1)", "BBBBBB")
            sage: sg, r1, r2 = vt.strebel_graph(mapping=True)
            sage: sg
            StrebelGraph("(0)(1,2,3,4)(~2,~4,5)(~3,~5)")
            sage: assert all(vt.face_angle(r2[h]) == sg.face_angle(h) for h in sg.half_edges())
        """
        if not self.is_strebel(slope=slope):
            raise ValueError('triangulation is not Strebel')

        n = 2 * self._ne
        ep = self._ep
        fp = self._fp
        vp = self._vp
        bdry = self._bdry
        colouring = self._colouring

        dim = self.stratum_dimension()
        m = 2 * dim # number of half-edges

        # index of half-edges that remain in the strebel graph
        index_strebel = array('i', [-1] * n)
        j = 0
        for e in range(0, n, 2):
            E = ep(e)
            if e == E:
                if self.is_half_edge_strebel(e, slope=slope):
                    index_strebel[e] = j
                    j += 2
            else:
                if self.is_half_edge_strebel(e, slope=slope) and self.is_half_edge_strebel(E, slope=slope):
                    index_strebel[e] = j
                    index_strebel[E] = j + 1
                    j += 2

        assert j == m, (j, m)

        # build vertex permutation, edge permutation, angle excess and nodes
        vertex_permutation = array('i', [-1] * m)
        beta = array('i', [0] * m)
        for e0, i in enumerate(index_strebel):
            if i == -1:
                continue
            assert index_strebel[ep(e0)] != -1
            e = e0
            j = -1
            sum_alpha_e = 0
            while j == -1:
                sum_alpha_e += bdry[e]
                if bdry[e]: # make sure that the last edge (with label_e!= -1) does not counted
                    e_mark_0 = e
                e = vp[e]
                j = index_strebel[e]
            vertex_permutation[i] = j

            # compute beta_e w.r.t the colours of e0 and e:
            if sum_alpha_e == 0:
                beta[i] = 0
            else:
                if slope == VERTICAL:
                    if colouring[e_mark_0 // 2] == RED and colouring[vp[e_mark_0] // 2] == BLUE:
                        beta[i] = sum_alpha_e
                    else:
                        beta[i] = sum_alpha_e - 1
                elif slope == HORIZONTAL:
                    if colouring[e_mark_0 // 2] == BLUE and colouring[vp[e_mark_0] // 2] == RED:
                        beta[i] = sum_alpha_e
                    else:
                        beta[i] = sum_alpha_e - 1

        from .strebel_graph import StrebelGraph
        sg = StrebelGraph.from_permutations(vertex_permutation, None, (beta,), (), mutable=mutable, check=True)

        if mapping:
            # Each edge in the Strebel graph is mapped to a sub-edge of
            # the veering triangulation at the boundary. We compute
            # this map below.
            strebel_to_veering_boundary = array('i', [-1] * m)
            for h in range(2 * self._ne):
                if self._bdry[h]:
                    k = h
                    while index_strebel[k] == -1:
                        k = self.previous_at_vertex(k)
                    strebel_to_veering_boundary[index_strebel[k]] = h

            for k, h in enumerate(strebel_to_veering_boundary):
                if h == -1:
                    continue
                k = sg._fp[k]
                while strebel_to_veering_boundary[k] == -1:
                    strebel_to_veering_boundary[k] = h
                    k = sg._fp[k]

            return (sg, index_strebel, strebel_to_veering_boundary)

        return sg


class VeeringTriangulations:
    @staticmethod
    def L_shaped_surface(a1, a2, b1, b2, t1=0, t2=0):
        r"""
        Return the quotient of the L-shaped surface.

        The corresponding surface belongs to the quadratic stratum Q(1, -1^5) and
        its orientation double cover in H(2).

        EXAMPLES::

            sage: from veerer import *
            sage: T, s, t = VeeringTriangulations.L_shaped_surface(1, 1, 1, 1)
            sage: T
            VeeringTriangulation("(0,2,3)(~0,1,4)(~1,5,6)", "BRRBBBB")
            sage: s
            (0, 1, 1, 1, 1, 1, 0)
            sage: t
            (1, 0, 0, 1, 1, 1, 1)
            sage: T._set_subspace_constraints(T._constraint_check, s, VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, t, VERTICAL)

            sage: T, s, t = VeeringTriangulations.L_shaped_surface(2, 3, 4, 5, 1, 2)
            sage: T._set_subspace_constraints(T._constraint_check, s, VERTICAL)
            sage: T._set_subspace_constraints(T._constraint_check, t, VERTICAL)
        """
        # Return the (quotient by the hyperelliptic involution of the) L-shaped surface
        # together with the equations of the GL2R deformation
        #

        #       +----+
        #    ^  |    |
        #    |   |    |
        # b2 |    |    |
        #    |     |    |
        #    v      |    |
        #            +    +---------+
        #    ^       |              |
        #    |       |              |
        # b1 |       |              |
        #    |        |              |
        #    v        |              |
        #             +----+---------+
        #             <---> <------->
        #               a1      a2
        #
        #     <----><->
        #       t2  t1

        if not isinstance(a1, numbers.Integral) or \
           not isinstance(a2, numbers.Integral) or \
           not isinstance(b1, numbers.Integral) or \
           not isinstance(b2, numbers.Integral) or \
           not isinstance(t1, numbers.Integral) or \
           not isinstance(t2, numbers.Integral):
            raise TypeError("a1, a2, b1, b2, t1, t2 must be integers")
        a1 = int(a1)
        a2 = int(a2)
        b1 = int(b1)
        b2 = int(b2)
        if a1 <= 0 or a2 <= 0 or b1 <= 0 or b2 <= 0 or t1 < 0 or t2 < 0:
            raise ValueError("a1, a2, b1, b2 must be positive and t1, t2 non-negative")

        T = VeeringTriangulation("(0,2,3)(~0,1,4)(~1,5,6)", [BLUE, RED, RED, BLUE, BLUE, BLUE, BLUE])
        s = (t1, a1, a2, a2 + t1, a1 + t1, a1 + t2, t2)
        t = (b1, 0, 0, b1, b1, b2, b2)

        return T, s, t

    @staticmethod
    def ngon(n):
        #TODO: here we should include the Teichmueller curve constraints
        # (over the real part of cyclotomic fields)
        n = int(n)
        assert(n > 4 and n % 2 == 0)
        m = (n - 2) // 2
        T = [(i, 2*m+i, ~(i+1)) for i in range(m)] + \
            [(~0, ~(2*m), ~(m+1))] + \
            [(m+i, ~(2*m+i), ~(m+i+1)) for i in range(1, m-1)] + \
            [(2*m-1, ~(3*m-1), m)]
        colouring = [RED] * (2*m) + [BLUE] * m
        return VeeringTriangulation(T, colouring)
