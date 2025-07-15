r"""
Flat veering triangulations layout in the plane

This module is mostly intended for plotting features. A layout is defined by a
choice of a rooted spanning forest together with a coordinate for each root.
Each tree in the spanning forest corresponds to triangulated polygon.

Note:

- when graphviz generates a svg it specifies a given size with the
  attributes "width" and "height". This would better be redefined
  to width="100%".
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
import math
import itertools

from sage.misc import prandom
from sage.categories.fields import Fields
from sage.rings.all import RDF
from sage.modules.free_module import FreeModule
from sage.sets.disjoint_set import DisjointSet
from sage.modules.free_module import VectorSpace
from sage.misc.prandom import shuffle
from sage.plot.graphics import Graphics
from sage.plot.line import line2d
from sage.plot.polygon import polygon2d
from sage.plot.text import text
from sage.plot.bezier_path import bezier_path
from sage.plot.point import point2d

from .constants import BLUE, RED, PURPLE, GREEN, HORIZONTAL, VERTICAL, RIGHT, UP, DOWN
from .permutation import perm_init, perm_check, perm_on_list
from .misc import flipper_edge, flipper_edge_perm, flipper_nf_to_sage, flipper_nf_element_to_sage, det2, flipper_face_edge_perms
from .triangulation import Triangulation
from .veering_triangulation import VeeringTriangulation
from .flat_structure import FlatStructure, FlatVeeringTriangulation
from .flat_structure import slope

_Fields = Fields()

EDGE_COLORS = {
    BLUE: 'blue',
    RED: 'red',
    PURPLE: 'purple',
    GREEN: 'green'}

TIKZ_EDGE_COLORS = {
    BLUE: 'veeringblue',
    RED: 'veeringred',
    PURPLE: 'veeringpurple',
    GREEN: 'veeringgreen'}

TIKZ_FACE_COLORS = {
    BLUE: 'veeringblue!20',
    RED: 'veeringred!20'}


def is_convex(pts):
    r"""
    Return whether ``pts`` form a convex polygon ordered either clockwise or counterclockwise.

    EXAMPLES::

        sage: from veerer.layout import is_convex
        sage: V = VectorSpace(QQ, 2)
        sage: pts = [V((0, 0)), V((1, 0)), V((2, 0)), V((2, 1)), V((2, 2)), V((1, 3)), V((-1, 1))]
        sage: is_convex(pts)
        True
        sage: is_convex(pts[::-1])
        True

        sage: pts = [V((0, 0)), V((2, 0)), V((1, 0)), V((2, 1)), V((2, 2)), V((1, 3)), V((-1, 1))]
        sage: is_convex(pts)
        False
        sage: is_convex(pts[::-1])
        False

        sage: pts = [V((0,0)), V((0, 2)), V((1, 1)), V((-1, 1))]
        sage: is_convex(pts)
        False
        sage: is_convex(pts[::-1])
        False
    """
    n = len(pts)
    if n <= 2:
        return True

    sign = None
    for i in range(n):
        u = pts[i] - pts[(i + 1) % n]
        v = pts[(i + 2) % n] - pts[(i + 1) % n]
        if u.is_zero() or v.is_zero() or u == v:
            return False

        d = u[0] * v[1] - u[1] * v[0]
        if d > 0:
            if sign is None:
                sign = 1
            elif sign == -1:
                return False
        elif d < 0:
            if sign is None:
                sign = -1
            elif sign == 1:
                return False
        else:
            # alignment
            if u[0] * v[0] > 0 or u[1] * v[1] > 0:
                return False

    return True


class FlatVeeringTriangulationLayout(object):
    r"""
    A flat triangulation layout in the plane.

    A layout is determined by a rooted forest of the dual graph of the
    triangulation, together with a choice of position and orientation for each
    root (recall that triangles in a
    :class:`~veerer.flat_structure.FlatVeeringTriangulation` are defined up to
    translation and multiplication by +/- 1).

    EXAMPLES:

        sage: from veerer import *
        sage: from veerer.layout import FlatVeeringTriangulationLayout

    A can be built from a list of triangles and vectors::

        sage: triangles = [(0, 1, 2), (-1, -2, -3)]
        sage: x = [1, 2, 1]
        sage: y = [2, 1, 1]
        sage: fvt = FlatVeeringTriangulation(triangles, x, y)
        sage: layout = FlatVeeringTriangulationLayout(fvt)
        sage: layout
        FlatVeeringTriangulationLayout(FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", (1, 2, 1), (2, 1, 1)), [])
        sage: layout.greedy_gluing()
        sage: layout
        FlatVeeringTriangulationLayout(FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB", (1, 2, 1), (2, 1, 1)), [0])

    Or from a preexisting flat surface::

        sage: T = VeeringTriangulation("(0,1,2)(~0,~1,3)", "BRBB")
        sage: F = FlatVeeringTriangulation.from_coloured_triangulation(T)
        sage: F.layout()
        FlatVeeringTriangulationLayout(FlatVeeringTriangulation("(0,1,2)(~0,~1,3)", "BRBB", (1, 1, 2, 2), (2, 1, 1, 1)), [])
    """
    def __init__(self, flat_triangulation, forest=None):
        r"""
        INPUT:

        - flat_triangulation - a flat triangulation
        """
        if not isinstance(flat_triangulation, FlatStructure):
            raise TypeError("input must be a flat veering triangulation")

        if flat_triangulation.boundary_faces():
            raise NotImplementedError("no implementation of layout and plotting for triangulation with boundary")

        self._triangulation = flat_triangulation.copy(mutable=False)

        ne = flat_triangulation.num_edges()
        nt = flat_triangulation.num_triangles()

        self._faces = list(self._triangulation.triangles())
        self._half_edge_to_face = [None] * (2 * self._triangulation._ne)
        for i, (a, b, c) in enumerate(self._faces):
            self._half_edge_to_face[a] = i
            self._half_edge_to_face[b] = i
            self._half_edge_to_face[c] = i

        # for each edge e we use the following conventions
        # * 0: it does not belong to the forest
        # * 1: it does belong to the forest
        self._forest = [0] * self._triangulation._ne
        if forest is not None:
            for e in forest:
                self._forest[self._triangulation._check_edge(e)] = 1

        is_abelian, oris = flat_triangulation.is_abelian(certificate=True)
        if not is_abelian:
            self._orientations = [UP] * len(self._faces)
        else:
            self._orientations = []
            for i, (a, b, c) in enumerate(self._faces):
                o = oris[a] + oris[b] + oris[c]
                assert o == 1 or o == 2, (o, a, b, c, oris)
                if o == 2:
                    self._orientations.append(UP)
                else:
                    self._orientations.append(DOWN)

        self._V = FreeModule(self._triangulation.base_ring(), 2)

        self._check()

    def _check(self):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: T = VeeringTriangulation("(0,1,2)(~0,~1,3)", "BRRR")
            sage: assert T.is_core()
            sage: F = T.flat_structure_min().layout()
            sage: F._check()
        """
        self._triangulation._check()

    def __repr__(self):
        return 'FlatVeeringTriangulationLayout({}, {})'.format(self._triangulation, [e for e, is_present in enumerate(self._forest) if is_present])

    def connected_components(self):
        r"""
        Return the connected components of the forest and the list of
        complementary edges.

        EXAMPLES::

            sage: from veerer import FlatVeeringTriangulation, UP, DOWN
            sage: x = (1, 2, 1)
            sage: y = (2, 1, 1)
            sage: fvt = FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", x, y)
            sage: layout = fvt.layout()
            sage: layout.connected_components()
            ({{0}, {1}}, [0, 1, 2])
            sage: layout.glue(0)
            sage: layout.connected_components()
            ({{0, 1}}, [])
        """
        ep = self._triangulation._ep
        fp = self._triangulation._fp
        from sage.sets.disjoint_set import DisjointSet
        U = DisjointSet(len(self._faces))
        for i, triangle in enumerate(self._faces):
            for h in triangle:
                if self._forest[h // 2]:
                    U.union(self._half_edge_to_face[h], self._half_edge_to_face[ep(h)])

        complementary_edges = []
        for e in range(self._triangulation._ne):
            if fp[2 * e + 1] == -1:
                continue
            h0 = U.find(self._half_edge_to_face[2 * e])
            h1 = U.find(self._half_edge_to_face[2 * e + 1])
            if h0 != h1:
                complementary_edges.append(e)

        return U, complementary_edges

    def connected_component(self, i):
        ep = self._triangulation._ep
        todo = [i]
        cc = set([i])
        while todo:
            i = todo.pop()
            assert i in cc
            for h in self._faces[i]:
                if self._forest[h // 2]:
                    hh = ep(h)
                    ii = self._half_edge_to_face[hh]
                    if ii not in cc:
                        cc.add(ii)
                        todo.append(ii)
        return cc


    def _update_sign(self, signs, h):
        assert h in signs
        hh = self._triangulation._fp[h]

        if self._triangulation._colouring[h // 2] == self._triangulation._colouring[hh // 2]:
            s = (-signs[h][0], -signs[h][1])
        elif self._triangulation._colouring[h // 2] == RED:
            s = (-signs[h][0], signs[h][1])
        elif self._triangulation._colouring[h // 2] == BLUE:
            s = (signs[h][0], -signs[h][1])
        else:
            raise ValueError("can not propagate signs with PURPLE or GREEN colour")

        if hh in signs:
            assert signs[hh] == s
        else:
            signs[hh] = s

    def _update_position(self, signs, positions, h):
        assert h in positions
        hh = self._triangulation._fp[h]

        hh_pos = positions[h] + self._V((signs[h][0] * self._triangulation._x[h // 2],
                                         signs[h][1] * self._triangulation._y[h // 2]))
        if hh in positions:
            assert positions[hh] == hh_pos
        else:
            positions[hh] = hh_pos

    def signs_and_positions(self, root_half_edge, pos=None, orientation=None):
        r"""
        Return the position of each vertex in the component determined by ``root_half_edge``.

        The output is a pair of dictionaries ``(signs, positions)`` whose keys
        are the half-edges in the component of ``root_half_edge`` and the values are
        repsecitvely pairs ``(x_sign, y_sign)`` and ``(x_position, y_position)``.

        EXAMPLES::

            sage: from veerer import FlatVeeringTriangulation, UP, DOWN

            sage: x = (1, 2, 1)
            sage: y = (2, 1, 1)
            sage: fvt = FlatVeeringTriangulation("(0,1,2)(~0,~1,~2)", x, y)
            sage: layout = fvt.layout()
            sage: layout.signs_and_positions(0)
            ({0: (1, 1), 2: (-1, -1), 4: (1, -1)},
             {0: (0, 0), 2: (1, 2), 4: (-1, 1)})
            sage: layout.glue(0)
            sage: layout.signs_and_positions(0)
            ({0: (1, 1), 1: (-1, -1), 2: (-1, -1), 3: (1, 1), 4: (1, -1), 5: (-1, 1)},
             {0: (0, 0), 1: (1, 2), 2: (1, 2), 3: (0, 0), 4: (-1, 1), 5: (2, 1)})
        """
        root_face = self._half_edge_to_face[root_half_edge]

        if orientation is None:
            orientation = self._orientations[root_face]
        elif orientation != UP and orientation != DOWN:
            raise ValueError("invalid orientation of the root face")
        if pos is None:
            pos = self._V.zero()

        ep = self._triangulation._ep
        fp = self._triangulation._fp

        signs = {}
        positions = {}
        triangle = self._faces[root_face]
        colours = [self._triangulation._colouring[h // 2] for h in triangle]
        if colours[0] == BLUE and colours[1] == RED:
            l, r, d = triangle
        elif colours[1] == BLUE and colours[2] == RED:
            d, l, r = triangle
        elif colours[2] == BLUE and colours[0] == RED:
            r, d, l = triangle
        else:
            raise RuntimeError

        if orientation == UP:
            signs[l] = (1, -1)
            signs[r] = (1, 1)
        else:
            signs[l] = (-1, 1)
            signs[r] = (-1, -1)
        self._update_sign(signs, r)

        positions[root_half_edge] = pos
        self._update_position(signs, positions, root_half_edge)
        self._update_position(signs, positions, fp[root_half_edge])

        todo = [root_face]
        done = set()
        while todo:
            i = todo.pop()
            for h in self._faces[i]:
                if self._forest[h // 2] == 0:
                    continue
                hh = ep(h)
                signs[hh] = (-signs[h][0], -signs[h][1])
                positions[hh] = positions[fp[h]]
                j = self._half_edge_to_face[hh]
                if j not in done:
                    self._update_sign(signs, hh)
                    self._update_position(signs, positions, hh)
                    self._update_sign(signs, fp[hh])
                    self._update_position(signs, positions, fp[hh])
                    done.add(j)
                    todo.append(j)

        return signs, positions

    def glue(self, *args, check=True):
        r"""
        Add the given edge ``e`` to the forest.

        A ``ValueError`` is raised if adding ``e`` creates a cycle.
        """
        for e in args:
            if check:
                e = self._triangulation._check_edge(e)
            i = self._half_edge_to_face[2 * e]
            j = self._half_edge_to_face[2 * e + 1]
            if check and self.connected_component(i) == self.connected_component(j):
                raise ValueError("invalid edge e={}".format(e))
            self._forest[e] = 1

    def creates_overlap(self, e, check=True):
        r"""
        Return whether gluing ``e`` creates an overlap.

        EXAMPLES::

            sage: from veerer import *
            sage: faces = "(0,1,2)(~1,11,~3)(3,4,5)(~2,~5,12)(~4,13,14)(~13,~16,~17)(17,~0,~15)(15,16,~14)(~8,~10,~11)(6,7,8)(~7,~12,~9)(9,~6,10)"
            sage: colours = "RBRRRBRBRRBBBBRBBR"
            sage: fvt = VeeringTriangulation(faces, colours).flat_structure_min().layout()
            sage: fvt.creates_overlap(2)
            False
            sage: fvt.glue(2, 12, 7, 6, 0, 15)
            sage: fvt.creates_overlap(16)
            True
            sage: fvt.glue(17)
            sage: fvt.creates_overlap(14)
            False
        """
        if check:
            e = self._triangulation._check_edge(e)

        fp = self._triangulation._fp
        pos0 = self.signs_and_positions(2 * e)[1]
        pos1 = self.signs_and_positions(2 * e + 1, pos0[fp[2 * e]])[1]

        for h0, p0 in pos0.items():
            hh0 = fp[h0]
            pp0 = pos0[hh0]
            assert p0 != pp0
            for h1, p1 in pos1.items():
                hh1 = fp[h1]
                pp1 = pos1[hh1]
                assert p1 != pp1

                if h0 // 2 == h1 // 2 and p0 == pp1:
                    continue

                # TODO: make is_convex return a special value for alignment
                # ie, would like to differentiate
                # * interior-interior intersection
                # * etc
                if is_convex((p0, p1, pp0, pp1)):
                    return True
                else:
                    u = pp0 - p0
                    v = p1 - pp1
                    w = p0 - p1
                    if (u[0] * v[1] - u[1] * v[0] == 0 and
                        u[0] * w[1] - u[1] * w[0] == 0):
                        # four points are aligned
                        if p0[0] != pp0[0]:
                            assert p1[0] != pp1[0], (p0, pp0, p1, pp1)
                            # use x-projection
                            coord = 0
                        else:
                            # use y-projection
                            assert p0[1] != pp0[1], (p0, pp0, p1, pp1)
                            assert p1[1] != pp1[1], (p0, pp0, p1, pp1)
                            coord = 1

                        a0 = p0[coord]
                        b0 = pp0[coord]
                        a1 = p1[coord]
                        b1 = pp1[coord]
                        if a0 < b0:
                            if (a0 < a1 < b0 or a0 < b1 < b0 or 2 * a0 < a1 + b1 < b0):
                                return True
                        else:
                            assert b0 < a0, (a0, b0)
                            if (b0 < a1 < a0 or b0 < b1 < a0 or 2 * b0 < a1 + b1 < 2 * a0):
                                return True

        return False

    def non_overlapping_gluings(self):
        r"""
        Iterate through complementary edges that do not create an overlap.

        EXAMPLES::

            sage: from veerer import *
            sage: faces = "(0,1,2)(~1,11,~3)(3,4,5)(~2,~5,12)(~4,13,14)(~13,~16,~17)(17,~0,~15)(15,16,~14)(~8,~10,~11)(6,7,8)(~7,~12,~9)(9,~6,10)"
            sage: colours = "RBRRRBRBRRBBBBRBBR"
            sage: fvt = VeeringTriangulation(faces, colours).flat_structure_min().layout()
            sage: fvt.glue(2, 12, 7, 6, 0, 15)
            sage: list(fvt.non_overlapping_gluings())
            [3, 4, 5, 8, 10, 11, 13, 14, 17]
        """
        return [e for e in self.connected_components()[1] if not self.creates_overlap(e)]

    def greedy_gluing(self, root_face=0, algorithm="BFS"):
        r"""
        Try to aggregate other components to the given ``root_face``.

        INPUT:

        - ``root_face`` -- optional integer, default to ``0``

        - ``algorithm`` -- either ``"BFS"`` for breadth-first search or
          ``"DFS"`` for depth-first search or ``"random"`` for randomized

        EXAMPLES::

            sage: from veerer import *
            sage: faces = "(0,1,2)(~1,11,~3)(3,4,5)(~2,~5,12)(~4,13,14)(~13,~16,~17)(17,~0,~15)(15,16,~14)(~8,~10,~11)(6,7,8)(~7,~12,~9)(9,~6,10)"
            sage: colours = "RBRRRBRBRRBBBBRBBR"
            sage: fs = VeeringTriangulation(faces, colours).flat_structure_min()

            sage: layout = fs.layout()
            sage: layout.greedy_gluing(0, "BFS")
            sage: layout
            FlatVeeringTriangulationLayout(FlatVeeringTriangulation(..., [0, 1, 2, 3, 8, 10, 11, 12, 14, 15, 17])

            sage: layout = fs.layout()
            sage: layout.greedy_gluing(0, "DFS")
            sage: layout
            FlatVeeringTriangulationLayout(..., [0, 1, 2, 5, 7, 9, 10, 12, 13, 15, 17])

            sage: layout = VeeringTriangulation(faces, colours).flat_structure_min().layout()
            sage: layout.greedy_gluing(0, "random")
            sage: layout
            FlatVeeringTriangulationLayout(...)
        """
        if algorithm not in ["BFS", "DFS", "random"]:
            raise ValueError("invalid algorithm")

        fp = self._triangulation._fp
        ep = self._triangulation._ep

        ccs, _ = self.connected_components()
        todo = collections.deque([i for i in range(len(self._faces)) if ccs.find(i) == ccs.find(root_face)])
        while todo:
            if algorithm == "BFS":
                i = todo.popleft()
            elif algorithm == "DFS":
                i = todo.pop()
            else:
                k = prandom.randrange(0, len(todo))
                todo[k], todo[-1] = todo[-1], todo[k]
                i = todo.pop()
            for h in self._faces[i]:
                j = ccs.find(self._half_edge_to_face[ep(h)])
                if self._forest[h // 2] or ccs.find(self._half_edge_to_face[h]) == j:
                    continue
                e = h // 2
                if fp[2 * e + 1] != -1 and not self.creates_overlap(e):
                    self.glue(e)
                    ccs.union(i, j)
                    todo.append(j)

    # TODO
    # def glue_cylinders(self)

    def unglue(self, e, check=True):
        r"""
        Remove the given edge ``e`` to the forest.
        """
        if check:
            e = self._triangulation._check_edge(e)
        self._forest[e] = 0

    def _edge_slope(self, e):
        e = self._check_edge(e)
        return slope(self._x[e], self._y[e])

    def _edge_is_boundary(self, e):
        r"""
        Test whether the edge ``e`` is on the boundary of the display.
        """
        if self._pos is None:
            return False
        fp = self._triangulation.face_permutation(copy=False)
        ep = self._triangulation.edge_permutation(copy=False)
        pos = self._pos
        vectors = self._triangulation._holonomies
        E = ep[e]
        return pos[fp[e]] is None or pos[E] is None or pos[fp[e]] != pos[E] or vectors[e] != -vectors[E]

    def _plot_edge(self, e, **opts):
        r"""
        Plot the edge ``e``.
        """
        assert self._pos is not None

        pos = self._pos
        fp = self._triangulation._fp
        ep = self._triangulation._ep

        oopts = {}
        E = ep[e]
        u = pos[e]
        v = pos[fp[e]]
        if not self._edge_is_boundary(e):
            # the edge is between adjacent faces
            oopts['alpha'] = 0.5
            oopts['linestyle'] = 'dotted'

        oopts['color'] = EDGE_COLORS[self._edge_slope(e)]

        oopts.update(opts)

        L = line2d([u, v], **oopts)


        return L

    def _tikz_edge(self, output, e, edge_label, **opts):
        r"""
        Plot the edge ``e``.
        """
        assert self._pos is not None
        assert edge_label is True or edge_label is False

        pos = self._pos
        fp = self._triangulation._fp
        ep = self._triangulation._ep

        E = ep[e]
        u = pos[e]
        v = pos[fp[e]]

        edge_tikz_opts = TIKZ_EDGE_COLORS[self._edge_slope(e)]
        if not self._edge_is_boundary(e):
            # the edge is between adjacent faces
            edge_tikz_opts += ',dotted'

        if edge_label:
            if self._edge_is_boundary(e) and e > E:
                lab = "$\\sim%d$" % (E)
            else:
                lab = "$%d$" % e

            output.write('\\draw[%s] (%s,%s) -- node[sloped] {\\contour{white}{%s}} (%s,%s);\n' % (edge_tikz_opts, u[0], u[1], lab, v[0], v[1]))

        else:
            output.write('\\draw[%s] (%s,%s) -- (%s,%s);\n' % (edge_tikz_opts, u[0], u[1], v[0], v[1]))

        if e == E:
            # folded edge
            output.write('\\draw mid +(.1,.1) -- (-.1,-.1);\n')
            output.write('\\draw mid +(-.1,.1) -- (.1,-.1);\n')

    def _plot_half_edge_label(self, a, pos, color="black", fontsize="medium", **opts):
        fp = self._triangulation._fp
        ep = self._triangulation._ep

        V = VectorSpace(RDF, 2)

        b = fp[a]
        c = fp[b]
        assert a in pos and b in pos and c in pos

        posa = V(pos[a])
        posb = V(pos[b])
        posc = V(pos[c])
        vc = posa - posc
        vc /= vc.norm()
        relposc = posa - vc

        if a % 2 == 0 and fp[a + 1] == -1:
            # folded edge
            pos = (7 * posa + 6 * posb + relposc) / 14
        else:
            pos = (8 * posa + 5 * posb + relposc) / 14

        lab = '~' + str(a // 2) if a % 2 else str(a // 2)

        x, y = posb - posa
        if y.is_zero():
            angle = 0
        elif x.is_zero():
            if y > 0:
                angle = 90
            else:
                angle = 270
        else:
            x = float(x)
            y = float(y)
            angle = math.acos(x / math.sqrt(x**2 + y**2))
            if y < 0:
                angle *= -1.0
            angle *= 180 / math.pi

        return text(lab, pos, rotation=angle, color=color, fontsize=fontsize)

    def _tikz_face(self, output, a,
            red='red!20', blue='blue!20', neutral='gray!20', tikz_face_options=None):
        assert self._pos is not None

        fp = self._triangulation.face_permutation(copy=False)
        b = fp[a]
        c = fp[b]
        pos = self._pos

        # computing slopes in order to determine filling color
        nred = nblue = 0
        for e in (a, b, c):
            slope = self._edge_slope(e)
            if slope == RED:
                nred += 1
            elif slope == BLUE:
                nblue += 1

        if nred == 2:
            color = TIKZ_FACE_COLORS[RED]
        elif nblue == 2:
            color = TIKZ_FACE_COLORS[BLUE]
        else:
            color = 'gray!20'

        output.write('\\fill[%s] (%s,%s) -- (%s,%s) -- (%s,%s) -- cycle;\n' % (
            color if tikz_face_options is None else color + ',' + tikz_face_options,
            pos[a][0], pos[a][1],
            pos[b][0], pos[b][1],
            pos[c][0], pos[c][1]))

    def _plot_train_track(self, slope, pos):
        V2 = VectorSpace(RDF, 2)
        G = Graphics()
        x = self._triangulation._x
        y = self._triangulation._y
        colouring = self._triangulation._colouring

        if slope == HORIZONTAL:
            POS = RED
            NEG = BLUE
            color = 'purple'
        else:
            POS = BLUE
            NEG = RED
            color = 'green'

        for i in self.connected_component(self._half_edge_to_face[next(iter(pos))]):
            h0, h1, h2 = self._faces[i]
            # determine the large edge
            e0 = h0 // 2
            e1 = h1 // 2
            e2 = h2 // 2
            col0 = colouring[e0]
            col1 = colouring[e1]
            col2 = colouring[e2]
            if col0 == POS and col1 == NEG:
                # e2 is large
                l, s1, s2 = h2, h0, h1
            elif col1 == POS and col2 == NEG:
                # i is large
                l, s1, s2 = h0, h1, h2
            elif col2 == POS and col0 == NEG:
                # j is large
                l, s1, s2 = h1, h2, h0
            else:
                raise RuntimeError(f"face=({h0}, {h1}, {h2}) col0={col0} col1={col1} col2={col2}")

            pl = V2(pos[l])
            ps1 = V2(pos[s1])
            ps2 = V2(pos[s2])

            cl = (pl + ps1) / 2
            vl = (ps1 - pl)
            cs1 = (ps1 + ps2) / 2
            vs1 = ps2 - ps1
            cs2 = (ps2 + pl) / 2
            vs2 = pl - ps2

            ol = V2((-vl[1], vl[0]))
            ol /= ol.norm()
            os1 = V2((-vs1[1], vs1[0]))
            os1 /= os1.norm()
            os2 = V2((-vs2[1], vs2[0]))
            os2 /= os2.norm()

            G += bezier_path([[cl, cl + 0.3 * ol,
                               cs1 + 0.3 * os1, cs1]], rgbcolor=color)
            G += bezier_path([[cl, cl + 0.3 * ol,
                               cs2 + 0.3 * os2, cs2]], rgbcolor=color)
        return G

    def _tikz_train_track(self, slope):
        raise NotImplementedError

    def positions(self, xshift=None, yshift=None, root_positions=None):
        ep = self._triangulation._ep
        fp = self._triangulation._fp
        colouring = self._triangulation._colouring
        if xshift is None:
            xshift = 0.0
        else:
            xshift = float(xshift)
        if yshift is None:
            yshift = 0.0
        else:
            yshift = float(yshift)
        xcur = 0.0
        shift = 0.5
        V2 = VectorSpace(RDF, 2)
        pos = {}
        for cc in self.connected_components()[0]:
            if root_positions is None:
                _, local_pos = self.signs_and_positions(self._faces[cc[0]][0])
                xmin = min(x for x, y in local_pos.values())
                xmax = max(x for x, y in local_pos.values())
                ymin = min(y for x, y in local_pos.values())
                ymax = max(y for x, y in local_pos.values())
                for h, (x, y) in local_pos.items():
                    pos[h] = V2((xshift + xcur - xmin + x, yshift + y - ymin))
                xcur += xmax - xmin + shift
            else:
                i = None
                for j in root_positions:
                    if self._half_edge_to_face[j] in cc:
                        i = j
                        break
                if i is None:
                    raise ValueError(f"no root position for component {cc}")
                v0 = V2(root_positions[j])
                _, local_pos = self.signs_and_positions(i)
                for h, (x, y) in local_pos.items():
                    pos[h] = v0 + V2((x, y))
        return pos

    # TODO: For edges whose two faces are plotted adjacent we should have an option to not display
    # the label
    def plot(self, horizontal_train_track=False, vertical_train_track=False, edge_labels=True, inner_edge_labels=True, outer_edge_labels=True, fill=True, xshift=None, yshift=None, root_positions=None):
        r"""
        Return a graphics.

        INPUT:

        - ``horizontal_train_track`` - boolean - whether to plot the horizontal
          train-track on the surface

        - ``vertical_train_track`` - boolean - whether to plot the vertical
          train-track on the surface

        EXAMPLES::

            sage: from veerer import *
            sage: faces = "(0, ~3, 4)(1, 2, ~7)(3, ~1, ~2)(5, ~8, ~4)(6, ~5, 8)(7, ~6, ~0)"
            sage: colours = 'RBRRBRBRB'
            sage: T = VeeringTriangulation(faces, colours)
            sage: FS = T.flat_structure_min().layout()
            sage: FS.plot(fill=False)
            Graphics object consisting of ... graphics primitives
            sage: FS.plot(fill=True)
            Graphics object consisting of ... graphics primitives
            sage: FS.plot(horizontal_train_track=True)
            Graphics object consisting of ... graphics primitives
            sage: FS.plot(vertical_train_track=True)
            Graphics object consisting of ... graphics primitives
        """
        ep = self._triangulation._ep
        fp = self._triangulation._fp
        colouring = self._triangulation._colouring
        G = Graphics()
        xcur = 0.0
        shift = 0.5
        V2 = VectorSpace(RDF, 2)
        pos = self.positions(xshift=xshift, yshift=yshift, root_positions=root_positions)
        for i in range(self._triangulation.num_triangles()):
            a, b, c = self._faces[i]
            G += polygon2d([pos[h] for h in self._faces[i]], color='gray', alpha=0.2)
            for h in self._faces[i]:
                edge_colour = 'red' if colouring[h // 2] == RED else 'blue'
                if h % 2 == 0 and fp[h + 1] == -1:
                    # folded edge
                    folded = True
                    G += line2d([pos[h], pos[fp[h]]], color=edge_colour)
                    # TODO: here matplotlib emit a warning, but it does not seem possible to set a markerfacecolor
                    G += point2d([(pos[h] + pos[fp[h]]) / 2], color='black', marker='x', pointsize=100)
                    if edge_labels and outer_edge_labels:
                        G += self._plot_half_edge_label(h, pos, fontsize="x-small")
                elif ep(h) not in pos or pos[fp[h]] != pos[ep(h)]:
                    # unglued edge
                    glued = False
                    G += line2d([pos[h], pos[fp[h]]], color=edge_colour)
                    if edge_labels and outer_edge_labels:
                        G += self._plot_half_edge_label(h, pos, fontsize="x-small")
                elif h % 2 == 0:
                    # edge in the forest (that we avoid plotting twice)
                    G += line2d([pos[h], pos[fp[h]]], linestyle='dotted', color=edge_colour)
                    if edge_labels and inner_edge_labels:
                        G += self._plot_half_edge_label(h, pos, fontsize="x-small")

        if horizontal_train_track:
            G += self._plot_train_track(HORIZONTAL, pos)

        if vertical_train_track:
            G += self._plot_train_track(VERTICAL, pos)

        G.set_aspect_ratio(1)
        G.axes(False)
        return G

    def tikz(self, filename=None, horizontal_train_track=False, vertical_train_track=False, edge_labels=True):
        if filename is None:
            from sys import stdout as output
        else:
            output = open(filename, 'w')

        n = self._triangulation.num_half_edges()
        fp = self._triangulation.face_permutation(copy=False)
        ep = self._triangulation.edge_permutation(copy=False)

        # 1. plot faces
        for e in range(n):
            if e < fp[e] and e < fp[fp[e]]:
                self._tikz_face(output, e)

        # 2. plot edges
        for e in range(n):
            if self._edge_is_boundary(e) or e <= ep[e]:
                self._tikz_edge(output, e, edge_labels)

        # 3. possibly plot train tracks
        if horizontal_train_track:
            self._tikz_train_track(output, HORIZONTAL)
        if vertical_train_track:
            self._tikz_train_track(output, VERTICAL)

        if filename is not None:
            output.close()
