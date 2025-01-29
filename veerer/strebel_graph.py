r"""
Strebel graphs
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024 Vincent Delecroix
#                     2024 Kai Fu
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

from array import array
import itertools
import numbers

from sage.structure.element import Matrix
from sage.rings.integer_ring import ZZ
from sage.matrix.constructor import matrix
from sage.matrix.special import identity_matrix

from .permutation import perm_check, perm_cycles, perm_cycles_to_string, str_to_cycles_and_data, perm_orbit
from .triangulation import face_boundary_init, Triangulation
from .constellation import Constellation
from .constants import *
from veerer.polyhedron import *


def one_edge_completion(t, angle_excess, colouring):
    r"""
    Return a pair of triples ``(new_t, new_angle_excess, new_colouring)`` corresponding to
    adding an edge forming a triangle with the two allowed colours.

    INPUT:

    - ``t`` -- a :class:`Triangulation` (with boundary)

    - ``angle_excess`` -- an array of angle excess

    - ``colouring`` -- an array of RED, BLUE colouring

    EXAMPLES::

        sage: from array import array
        sage: from veerer import Triangulation
        sage: from veerer.strebel_graph import one_edge_completion
        sage: t = Triangulation("", "(0:1)(1:1)(~0:1,~1:1)")
        sage: colouring = [2, 1]
        sage: angle_excess = array('i', [3, 0, 3, 3])
        sage: one_edge_completion(t, angle_excess, colouring)
        ((Triangulation("(~0,2,~1)(0:1)(1:1)(~2:1)"),
          array('i', [3, 0, 3, 0, 0, 3]),
          array('i', [2, 1, 1])),
         (Triangulation("(~0,2,~1)(0:1)(1:1)(~2:1)"),
          array('i', [3, 0, 3, 0, 0, 3]),
          array('i', [2, 1, 2])))
    """
    # We insert the (m, M)-edge as follows
    #
    #   x
    #   |
    #   |
    #   |c
    #   |
    #   x
    #   | \ M
    #   |A   \
    #   |       \
    #  a|  e      m\   b
    #   x-----------x-----------x
    #             E           B

    n = 2 * t._ne
    vp = t._vp
    ep = t._ep
    fp = t._fp
    bdry = t._bdry
    m = n     # new positive half-edge
    M = n + 1 # new negative half-edge

    for x in range(1, n, 2):
        if vp[x] == -1:
            assert bdry[x] == angle_excess[x] == 0

    found = False
    for e in range(n):
        if bdry[e] and angle_excess[e] == 0:
            found = True
            break
    if not found:
        raise ValueError('already complete')

    E = e ^ 1 if vp[e ^ 1] != -1 else e
    a = vp[e]
    A = a ^ 1 if vp[a ^ 1] != -1 else a
    b = fp[e]
    c = vp[A]
    C = c ^ 1 if vp[c ^ 1] != -1 else c

    # build the new triangle face (e, m, A)
    newvp = array('i', vp)
    newfp = array('i', fp)

    newvp.append(-1)
    newvp.append(-1)
    newfp.append(-1)
    newfp.append(-1)

    newfp[e] = m
    newfp[m] = A
    newvp[A] = M
    newvp[m] = E

    is_bigon = c == E
    assert is_bigon == (b == A)

    if is_bigon:
        newfp[M] = M
        newvp[M] = m
        newvp[b] = M
    else:
        newfp[C] = M
        newfp[M] = b
        newvp[M] = c
        newvp[b] = m

    # new bdry: m is internal, M is boundary and e and A becomes internal
    newbdry = bdry[:]
    newbdry.append(0)
    newbdry.append(1)

    assert newbdry[e] == 1
    assert newbdry[A] == 1
    newbdry[e] = newbdry[A] = 0

    # build new colourings
    colouring1 = array('i', colouring)
    colouring1.append(-1)

    # claim: a and e must have different colours
    # (so that both RED and BLUE are allowed for the new edge (m, M)
    assert colouring1[a // 2] != colouring1[e // 2]

    colouring2 = colouring1[:]
    colouring1[-1] = RED
    colouring2[-1] = BLUE

    # build new angle excesses
    angle_excess1 = angle_excess[:]
    angle_excess1.append(-1)
    angle_excess1.append(-1)
    angle_excess1[M] = angle_excess1[A]
    angle_excess1[A] = angle_excess1[m] = 0

    angle_excess2 = angle_excess1[:]

    if not is_bigon:
        col_a = colouring1[a // 2]
        col_b = colouring1[b // 2]
        col_c = colouring1[c // 2]
        col_e = colouring1[e // 2]

        if col_a == BLUE:
            assert col_e == RED
            if col_b == RED:
                angle_excess2[b] -= 1
            if col_c == BLUE:
                angle_excess1[M] -= 1
        else:
            assert col_a == RED and col_e == BLUE
            if col_b == BLUE:
                angle_excess1[b] -= 1
            if col_c == RED:
                angle_excess2[M] -= 1

    t = Triangulation.from_permutations(newvp, newfp, (newbdry,), mutable=False, check=False)
    for e in range(1, n + 2, 2):
        if t._vp[e] == -1:
            assert newbdry[e] == angle_excess1[e] == angle_excess2[e] == 0

    return ((t, angle_excess1, colouring1), (t, angle_excess2, colouring2))


class StrebelGraph(Constellation):
    r"""
    Strebel graph.

    A Strebel graph encodes a specific saddle connection configuration
    associated to a meromorphic Abelian or quadratic differential on a Riemann
    surface. It is encoded as an embedded graph on a surface (ie a triple of
    permutations ``vp``, ``ep`` and ``fp`` for respectively the vertex, edge
    and face permutations) together with a half plane excess in each corner (a
    non-negative integer).

    EXAMPLES::

        sage: from veerer import StrebelGraph

        sage: StrebelGraph("(0,~0:1)")
        StrebelGraph("(0,~0:1)")
    """
    __slots__ = ['_excess']

    def __init__(self, faces, excess=None, mutable=False, check=True):
        if isinstance(faces, StrebelGraph):
            fp = faces.face_permutation(copy=True)
            ep = faces.edge_permutation(copy=True)
            excess = faces.half_plane_excess(copy=True)
        else:
            fp, excess = face_boundary_init(faces, excess)

        Constellation.__init__(self, len(fp) // 2, None, fp, (excess,), (), mutable, check)

    def _check_vertex_separatrix(self, half_edge, angle):
        half_edge = self._check_half_edge(half_edge)
        if not isinstance(angle, numbers.Integral):
            raise ValueError("invalid angle for separatrix")
        angle = int(angle)
        if angle < 0 or angle > self._excess[half_edge]:
            raise ValueError("angle (={}) out of range for separatrix; must be >= 0 and <= {}".format(angle, self._excess[half_edge]))

    def boundary_half_edges(self):
        return self.half_edges()

    def _set_data_pointers(self):
        self._excess = self._half_edges_data[0]

    def half_plane_excess(self, copy=True):
        return self._excess[:] if copy else self._excess

    boundary_faces = Constellation.faces
    num_boundary_faces = Constellation.num_faces

    def base_ring(self):
        from sage.rings.integer_ring import ZZ
        return ZZ

    def __str__(self):
        r"""
        Return the string representation.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: T = StrebelGraph("(0,1,2)(~0,~1:1,~2:2)")
            sage: str(T)
            'StrebelGraph("(0,1,2)(~0,~1:1,~2:2)")'
        """
        bdry_cycles = perm_cycles_to_string(perm_cycles(self._fp, 2*self._ne), edge_like=True, data=self._excess)
        return 'StrebelGraph("%s")' % bdry_cycles

    def __repr__(self):
        return str(self)

    def is_abelian(self, certificate=False):
        r"""
        Return whether this Strebel graph is Abelian.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: StrebelGraph("(0:1,1:1,2)(~2,~3:1,~4:1)(3,~1,5)(~0,4,~5)").is_abelian()
            True
            sage: StrebelGraph("(0:1,1,2)(~2,~3,~4:1)(3,~1:1,5)(~0:1,4,~5)").is_abelian()
            False
        """
        ep = self._ep
        vp = self._vp

        if self.has_folded_edge():
            return (False, None) if certificate else False

        # Try to give a coherent holonomy with signs for each half edge. To
        # each half edge is associated a boolean
        #   True: for positive coordinates
        #   False: for negative coordinates
        # The half-edge orientations is propagated walking along edges and
        # vertices.

        oris = [None] * (2 * self._ne)  # list of orientations decided so far
        oris[0] = True
        oris[ep(0)] = False
        q = [0, ep(0)]  # queue of half-edges to be treated

        while q:
            e = q.pop()
            o = oris[e]
            assert o is not None
            f = vp[e]
            while True:
                # propagate orientation
                if self._excess[e] % 2 == 0:
                    o = not o

                if oris[f] is None:
                    assert oris[ep(f)] is None
                    oris[f] = o
                    oris[ep(f)] = not o
                    q.append(ep(f))
                elif oris[f] != o:
                    return (False, None) if certificate else False
                else:
                    break

                e, f = f, vp[f]

        return (True, oris) if certificate else True

    def vertex_separatrices(self, flat=True):
        r"""
        Return the pairs ``(h, a)`` encoding vertex separatrices on this Strebel graph.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: sg = StrebelGraph("(0,1,2,3)(~1,~0:1,~3:2,~2:1)")
            sage: sg.vertex_separatrices()
            [(0, 0),
             (7, 0),
             (7, 1),
             (7, 2),
             (1, 0),
             (1, 1),
             (2, 0),
             (3, 0),
             (4, 0),
             (5, 0),
             (5, 1),
             (6, 0)]
            sage: seps = sg.vertex_separatrices(flat=False)
            sage: seps
            [[(0, 0), (7, 0), (7, 1), (7, 2)],
             [(1, 0), (1, 1), (2, 0)],
             [(3, 0), (4, 0)],
             [(5, 0), (5, 1), (6, 0)]]
            sage: all(sg.vertex_angle(h) == len(sep) for sep in seps for h, a in sep)
            True
        """
        separatrices = []
        for cycle in self.vertices():
            orbit = []
            for h in cycle:
                for a in range(self._excess[h] + 1):
                    orbit.append((h, a))
            if flat:
                separatrices.extend(orbit)
            else:
                separatrices.append(orbit)
        return separatrices

    # TODO: (for Kai) should we go clockwise or counter-clockwise around the face
    # TODO: (for Kai) what should we do for angle=0 (ie infinite cylinder) faces
    # which have no associated separatrices?
    def face_separatrices(self, flat=True):
        r"""
        Return the pairs ``(h, a)`` encoding face separatrices on this Strebel graph.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: sg = StrebelGraph("(0,1,2)(~0,~1:1,~2:2)")
            sage: sg.face_separatrices()
            [(3, 0), (5, 1), (5, 0)]
            sage: seps = sg.face_separatrices(flat=False)
            sage: seps
            [[(3, 0), (5, 1), (5, 0)]]
            sage: all(sg.face_angle(h) == -len(sep) for sep in seps for h, a in sep)
            True

        An example in H(1^2, -1^2) where the two faces have no separatrices::

            sage: sg = StrebelGraph("(0,1,2,3)(~0,~1,~2,~3)")
            sage: sg.face_separatrices(flat=False)
            []
            sage: sg.face_separatrices(flat=True)
            []
        """
        separatrices = []
        for cycle in self.faces():
            orbit = []
            for h in cycle:
                for a in range(self._excess[h] -1, -1, -1):
                    orbit.append((h, a))
            if orbit:
                if flat:
                    separatrices.extend(orbit)
                else:
                    separatrices.append(orbit)
        return separatrices

    def stratum(self):
        r"""
        Return the stratum of Abelian or quadratic differentials of this Strebel graph.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: StrebelGraph("(0,1,2)(~0,~1:1,~2:2)").stratum()  # optional - surface_dynamics
            Q_1(7, -2, -5)
            sage: StrebelGraph("(0,1)").stratum()  # optional - surface_dynamics
            Q_0(0, -1^2, -2)

        A non-connected example::

            sage: StrebelGraph("(0,~2:1,~0,2:1)(1:1,3,~1:1,~3)").stratum()  # optional - surface_dynamics
            (H_1(2, -2), H_1(2, -2))

        Example with folded edges::

            sage: StrebelGraph("(0,1,2,3)").stratum()  # optional - surface_dynamics
            Q_0(2, -1^4, -2)
        """
        if not self.is_connected():
            return tuple(component.stratum() for component in self.connected_components_subgraphs())

        # folded edges
        num_folded_edges = self.num_folded_edges()

        # degrees of holomorphic part
        hol = [len(v) - 2 + sum(self._excess[i] for i in v) for v in self.vertices()]

        # degrees of meromorphic part
        mer = [-2 - sum(self._excess[i] for i in f) for f in self.faces()]

        # Determine whether it is Abelian (k=1) or quadratic (k=2) stratum
        if num_folded_edges or any(x % 2 for x in hol) or any(x % 2 for x in mer) or not self.is_abelian():
            k  = 2
        else:
            hol = [x // 2 for x in hol]
            mer = [x // 2 for x in mer]
            k = 1

        from surface_dynamics import Stratum
        return Stratum(hol + [-1] * num_folded_edges + mer, k)

    def abelian_cover(self, mutable=False, involution_and_quotient=False):
        r"""
        Return the orientation double cover of this Strebel graph.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: sg = StrebelGraph("(0:1,1,2)(~2,~3,~4:1)(3,~1:1,5)(~0:1,4,~5)")
            sage: sg.abelian_cover()
            StrebelGraph("(0:1,1,2,~6:1,~7,~8)(~0:1,~10,~5,6:1,4,11)(~1:1,~11,~9,7:1,5,3)(~2,~3,10:1,8,9,~4:1)")
            sage: print(sg.stratum(), sg.abelian_cover().stratum())  # optional - surface_dynamics
            Q_0(2^4, -3^4) H_1(1^8, -2^4)

            sage: StrebelGraph("(0)").abelian_cover()
            StrebelGraph("(0)(~0)")
            sage: StrebelGraph("(0:1)").abelian_cover()
            StrebelGraph("(0:1,~0:1)")
            sage: StrebelGraph("(0,~0)").abelian_cover()
            StrebelGraph("(0,1)(~0,~1)")
        """
        vp = self._vp

        n = (4 * self._ne - 2 * self.num_folded_edges())

        j = 2 * self._ne
        inv = array('i', [-1] * (2 * self._ne))  # involution on the cover
        quot = array('i', [-1] * n)  # quotient map
        excess_cov = array('i', [-1] * n)
        for e in range(self._ne):
            quot[2 * e] = 2 * e
            if self._vp[2 * e + 1] == -1:
                inv[2 * e] = 2 * e + 1
                excess_cov[2 * e] = excess_cov[2 * e + 1] = self._excess[2 * e]
                quot[2 * e + 1] = 2 * e
            else:
                excess_cov[2 * e] = excess_cov[j + 1] = self._excess[2 * e]
                excess_cov[2 * e + 1] = excess_cov[j] = self._excess[2 * e + 1]
                inv[2 * e] = j + 1
                inv[2 * e + 1] = j
                quot[2 * e + 1] = 2 * e + 1
                quot[j] = 2 * e + 1
                quot[j + 1] = 2 * e
                j += 2

        vp_cov = array('i', [-1] * n)
        for e in range(2 * self._ne):
            f = vp[e]
            if f == -1:
                continue
            if ((self._excess[e] % 2 == 0) + (e % 2 != f % 2)) % 2:
                vp_cov[e] = inv[f]
                vp_cov[inv[e]] = f
            else:
                vp_cov[e] = f
                vp_cov[inv[e]] = inv[f]

        sg_cov = StrebelGraph.from_permutations(vp_cov, None, (excess_cov,), mutable=mutable, check=False)
        return (sg_cov, inv, quot) if involution_and_quotient else sg_cov

    def as_linear_family(self):
        r"""
        Return this Strebel graph as a linear family.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: G = StrebelGraph("(0,1,2)(~0,~1:1,~2:2)")
            sage: G.as_linear_family()
            StrebelGraphLinearFamily("(0,1,2)(~0,~1:1,~2:2)", [(1, 0, 0), (0, 1, 0), (0, 0, 1)])
        """
        from sage.matrix.special import identity_matrix
        from .linear_family import StrebelGraphLinearFamily
        return StrebelGraphLinearFamily(self, identity_matrix(ZZ, self.num_edges()))

    def angle_excess(self, colouring, slope=VERTICAL):
        r"""
        Return the angle excess of the corners of the associated colouring.

        This function is mostly intended to be a technical steps in
        constructing the veering triangulations associated to a Strebel graph.
        See :meth:`veering_triangulations`.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: G = StrebelGraph("(0,1,2)(~0,~1:1,~2:2)")
            sage: for colouring in G.colourings():
            ....:     print(colouring, G.angle_excess(colouring))
            array('i', [1, 1, 1]) array('i', [1, 1, 1, 2, 1, 3])
            array('i', [1, 1, 2]) array('i', [0, 0, 1, 2, 1, 3])
            array('i', [1, 2, 1]) array('i', [1, 1, 1, 2, 0, 2])
            array('i', [1, 2, 2]) array('i', [0, 0, 1, 2, 1, 3])
            array('i', [2, 1, 1]) array('i', [1, 1, 0, 1, 1, 3])
            array('i', [2, 1, 2]) array('i', [1, 1, 0, 1, 1, 3])
            array('i', [2, 2, 1]) array('i', [1, 1, 1, 2, 0, 2])
            array('i', [2, 2, 2]) array('i', [1, 1, 1, 2, 1, 3])

            sage: G = StrebelGraph("(0,1,~1)")
            sage: for colouring in G.colourings():
            ....:     print(colouring, G.angle_excess(colouring))
            array('i', [1, 1]) array('i', [1, 0, 1, 1])
            array('i', [1, 2]) array('i', [0, 0, 1, 1])
            array('i', [2, 1]) array('i', [1, 0, 0, 1])
            array('i', [2, 2]) array('i', [1, 0, 1, 1])
        """
        # remark: red-red corners with angle excess 0 and 1 both correspond
        # to zero half-plane excess.
        # claim: it is impossible to have a red-red corner with 0 angle
        # excess in a strebel graph.

        n = 2 * self._ne
        vp = self._vp
        alpha = array('i', self._excess)

        for e in range(n):
            e1 = vp[e]
            if (e1 != -1) and ((slope == VERTICAL and (colouring[e // 2] != RED or colouring[e1 // 2] != BLUE)) or \
               (slope == HORIZONTAL and (colouring[e // 2] != BLUE or colouring[e1 // 2] != RED))):
                alpha[e] += 1

        return alpha

    def colourings(self):
        r"""
        Run through the red, blue colourings of this Strebel graph.

        Each colouring consists of an array of length the number of half-edges.

        EXAMPLES::

            sage: from veerer import StrebelGraph

            sage: G = StrebelGraph("(0,1,2)(~0,~1:1,~2:2)")
            sage: list(G.colourings())
            [array('i', [1, 1, 1]),
             array('i', [1, 1, 2]),
             array('i', [1, 2, 1]),
             array('i', [1, 2, 2]),
             array('i', [2, 1, 1]),
             array('i', [2, 1, 2]),
             array('i', [2, 2, 1]),
             array('i', [2, 2, 2])]

            sage: G = StrebelGraph("(0,1,2,3)")
            sage: list(G.colourings())
            [array('i', [1, 1, 1, 1]),
             array('i', [1, 1, 1, 2]),
             ...
             array('i', [2, 2, 2, 1]),
             array('i', [2, 2, 2, 2])]
        """
        return (array('i', x) for x in itertools.product([RED, BLUE], repeat=self._ne))

    def _set_strebel_constraints(self, insert, x):
        for v in x:
            insert(v >= 0)

    def cone(self, backend=None):
        r"""
        Return the cone of x-coordinates for this Strebel graph.

        EXAMPLES::

            sage: from veerer import StrebelGraph, VERTICAL, HORIZONTAL
            sage: G = StrebelGraph("(0)(~0)")

            sage: C = G.cone()
            sage: C
            Cone of dimension 1 in ambient dimension 1 made of 1 facets (backend=ppl)
            sage: C.rays()
            [[1]]

            sage: sg = StrebelGraph("(~1:1,~0,1:1,0)")
            sage: sg.cone(backend='ppl')
            Cone of dimension 2 in ambient dimension 2 made of 2 facets (backend=ppl)
            sage: sg.cone(backend='sage')
            Cone of dimension 2 in ambient dimension 2 made of 2 facets (backend=sage)
            sage: sg.cone(backend='normaliz-QQ')  # optional - pynormaliz
            Cone of dimension 2 in ambient dimension 2 made of 2 facets (backend=normaliz-QQ)
        """
        from .polyhedron import LinearExpressions, ConstraintSystem
        L = LinearExpressions(self.base_ring())
        ne = self.num_edges()
        x = [L.variable(i) for i in range(ne)]
        cs = ConstraintSystem(ne)
        self._set_strebel_constraints(cs.insert, x)
        return cs.cone(backend=backend)

    def veering_triangulations(self, colouring, slope=VERTICAL, mutable=False):
        r"""
        Run through Strebel-veering triangulations obtained by completing this
        Strebel graph given the ``colouring`` of its edges.

        EXAMPLES::

            sage: from veerer import *
            sage: examples = []
            sage: examples.append(StrebelGraph("(~1:1,~0,1:1,0)"))
            sage: examples.append(StrebelGraph("(0,~1)(1)(~0)"))
            sage: examples.append(StrebelGraph("(0:2)(1:2)(~1,~0:2)"))
            sage: examples.append(StrebelGraph("(0,1,2,3)"))
            sage: for G in examples:  # optional - surface_dynamics
            ....:     print(G.stratum())
            H_1(2, -2)
            H_0(1, -1^3)
            H_0(4, -2^3)
            Q_0(2, -1^4, -2)

            sage: for G in examples:
            ....:     print(G)
            ....:     for colouring in G.colourings():
            ....:         vts = G.veering_triangulations(colouring)
            ....:         assert all(vt.strebel_graph() == G for vt in vts)
            ....:         assert all(vt.stratum() == G.stratum() for vt in vts)  # optional - surface_dynamics
            ....:         print(colouring, list(G.veering_triangulations(colouring)))
            StrebelGraph("(0,~1:1,~0,1:1)")
            array('i', [1, 1]) [VeeringTriangulation("(0:1,~1:2,~0:1,1:2)", "RR")]
            array('i', [1, 2]) [VeeringTriangulation("(0,2,1)(~0,3,~1)(~2:2,~3:1)", "RBBR"), VeeringTriangulation("(0,2,1)(~0,3,~1)(~2:2,~3:2)", "RBBB"), VeeringTriangulation("(0,2,1)(~0,3,~1)(~2:2,~3:2)", "RBRR"), VeeringTriangulation("(0,2,1)(~0,3,~1)(~2:1,~3:2)", "RBRB")]
            array('i', [2, 1]) [VeeringTriangulation("(0:1,~1:1,~0:1,1:1)", "BR")]
            array('i', [2, 2]) [VeeringTriangulation("(0:1,~1:2,~0:1,1:2)", "BB")]
            StrebelGraph("(0,~1)(~0)(1)")
            array('i', [1, 1]) [VeeringTriangulation("(0:1,~1:1)(~0:1)(1:1)", "RR")]
            array('i', [1, 2]) [VeeringTriangulation("(0,2,~1)(~0:1)(1:1)(~2:1)", "RBR"), VeeringTriangulation("(0,2,~1)(~0:1)(1:1)(~2:1)", "RBB")]
            array('i', [2, 1]) [VeeringTriangulation("(0,~1,2)(~0:1)(1:1)(~2:1)", "BRR"), VeeringTriangulation("(0,~1,2)(~0:1)(1:1)(~2:1)", "BRB")]
            array('i', [2, 2]) [VeeringTriangulation("(0:1,~1:1)(~0:1)(1:1)", "BB")]
            StrebelGraph("(0:2)(~0:2,~1)(1:2)")
            array('i', [1, 1]) [VeeringTriangulation("(0:3)(~0:3,~1:1)(1:3)", "RR")]
            array('i', [1, 2]) [VeeringTriangulation("(0:3)(~0:2,~1:1)(1:3)", "RB")]
            array('i', [2, 1]) [VeeringTriangulation("(~0,~1,2)(0:3)(1:3)(~2:3)", "BRR"), VeeringTriangulation("(~0,~1,2)(0:3)(1:3)(~2:3)", "BRB")]
            array('i', [2, 2]) [VeeringTriangulation("(0:3)(~0:3,~1:1)(1:3)", "BB")]
            StrebelGraph("(0,1,2,3)")
            array('i', [1, 1, 1, 1]) [VeeringTriangulation("(0:1,1:1,2:1,3:1)", "RRRR")]
            array('i', [1, 1, 1, 2]) [VeeringTriangulation("(0,4,3)(1:1,2:1,~4:1)", "RRRBR"), VeeringTriangulation("(0,4,3)(1,5,~4)(2:1,~5:1)", "RRRBBR"), VeeringTriangulation("(0,4,3)(1,5,~4)(2,6,~5)(~6:1)", "RRRBBBR"), VeeringTriangulation("(0,4,3)(1,5,~4)(2,6,~5)(~6:1)", "RRRBBBB")]
            ...
            array('i', [2, 2, 2, 2]) [VeeringTriangulation("(0:1,1:1,2:1,3:1)", "BBBB")]
        """
        def is_complete(t, angle_excess, colouring):
            return not any(b1 and b2 == 0 for (b1, b2) in zip(t._bdry, angle_excess))

        n = 2 * self._ne
        angle_excess = self.angle_excess(colouring, slope=slope)
        bdry = array('i', [1] * n)
        for e in range(1, n, 2):
            if self._vp[e] == -1:
                bdry[e] = 0
        t0 = Triangulation.from_permutations(self._vp[:], self._fp[:], (bdry,), mutable=False, check=True)
        T = (t0, angle_excess, colouring)
        complete = []
        incomplete = []
        if is_complete(*T):
            complete.append(T)
        else:
            incomplete.append(T)

        while incomplete:
            T = incomplete.pop()
            for TT in one_edge_completion(*T):
                if is_complete(*TT):
                    complete.append(TT)
                else:
                    incomplete.append(TT)

        from .veering_triangulation import VeeringTriangulation
        for t, angle_excess, colouring in complete:
            vp = t._vp
            fp = t._fp
            cols = array('i', colouring)
            yield VeeringTriangulation.from_permutations(vp, fp, (angle_excess,), (cols,), mutable=mutable, check=True)

    def delaunay_triangulations(self, colouring, slope=VERTICAL, mutable=False, backend=None):
        r"""
        Run through the Delaunay Strebel-veering triangulations obtained by completing
        this Strebel graph given the ``colouring`` of its edges.

        EXAMPLES::

            sage: from veerer import *
            sage: examples = []
            sage: examples.append(StrebelGraph("(~1:1,~0,1:1,0)"))
            sage: examples.append(StrebelGraph("(0,2,~1)(1)(~2,~0)"))
            sage: examples.append(StrebelGraph("(0:2,2,~1)(1,~0)(~2)"))
            sage: for G in examples:
            ....:     print(G)
            ....:     for colouring in G.colourings():
            ....:         print(colouring, sum(1 for _ in G.veering_triangulations(colouring)), sum(1 for _ in G.delaunay_triangulations(colouring)))
            StrebelGraph("(0,~1:1,~0,1:1)")
            array('i', [1, 1]) 1 1
            array('i', [1, 2]) 4 2
            array('i', [2, 1]) 1 1
            array('i', [2, 2]) 1 1
            StrebelGraph("(0,2,~1)(~0,~2)(1)")
            array('i', [1, 1, 1]) 1 1
            array('i', [1, 1, 2]) 6 5
            array('i', [1, 2, 1]) 3 3
            array('i', [1, 2, 2]) 6 5
            array('i', [2, 1, 1]) 6 3
            array('i', [2, 1, 2]) 3 3
            array('i', [2, 2, 1]) 6 3
            array('i', [2, 2, 2]) 1 1
            StrebelGraph("(0:2,2,~1)(~0,1)(~2)")
            array('i', [1, 1, 1]) 1 1
            array('i', [1, 1, 2]) 2 2
            array('i', [1, 2, 1]) 2 2
            array('i', [1, 2, 2]) 2 2
            array('i', [2, 1, 1]) 6 5
            array('i', [2, 1, 2]) 6 5
            array('i', [2, 2, 1]) 2 2
            array('i', [2, 2, 2]) 1 1
        """
        for vt in self.veering_triangulations(colouring, slope, mutable):
            if vt.is_delaunay(backend):
                yield vt

    def residue_matrix(self):
        r"""
        Return the residue matrix.

        The residue matrix allows to recover the values of residues given a vector
        of edge length. The number of rows is equal to the number of faces while
        the number of columns is the number of edges.

        As the sum of residues is zero, the sum of rows of the matrix vanishes.

        EXAMPLES::

            sage: from veerer import StrebelGraph

            sage: StrebelGraph("(0)(~0)").residue_matrix()
            [ 1]
            [-1]
            sage: StrebelGraph("(0,~1)(1)(~0)").residue_matrix()
            [ 1  1]
            [-1  0]
            [ 0 -1]
            sage: StrebelGraph("(0,2,~3,~1)(1)(3,~0)(~2)").residue_matrix()
            [ 1  1  1  1]
            [-1  0  0 -1]
            [ 0 -1  0  0]
            [ 0  0 -1  0]

            sage: StrebelGraph("(0:1,~0:1)").residue_matrix()
            [0]

            sage: StrebelGraph("(0:1,1:1,2)(~2,~3:1,~4:1)(3,~1,5)(~0,4,~5)").residue_matrix()
            [ 1 -1 -1  0  0  0]
            [-1  0  0  0 -1 -1]
            [ 0  1  0  1  0  1]
            [ 0  0  1 -1  1  0]

            sage: sg = StrebelGraph("(0:1,1,2)(~2,~3,~4:1)(3,~1:1,5)(~0:1,4,~5)")
            sage: sg.abelian_cover().residue_matrix()
            [ 1  1  1  0  0  0 -1 -1 -1  0  0  0]
            [-1  0  0  0  1 -1  1  0  0  0 -1  1]
            [ 0 -1  0  1  0  1  0  1  0 -1  0 -1]
            [ 0  0 -1 -1 -1  0  0  0  1  1  1  0]
        """
        nf = self.num_faces()
        ne = self.num_edges()
        r = matrix(ZZ, nf, ne)

        ans, orientations = self.is_abelian(certificate=True)
        if not ans:
            raise ValueError('not an Abelian differential')
        orientations = [1 if x else -1 for x in orientations]

        for i, f in enumerate(self.faces()):
            for h in f:
                r[i, h // 2] += orientations[h]

        return r

    def constraints_matrix(self, mutable=None):
        r"""
        Return a basis of constraints on x-coordinates as a matrix.

        As there is no constraints for a Strebel graph, the answer has no row.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: G = StrebelGraph("(0)(~0)")
            sage: G.constraints_matrix()
            []
            sage: G.constraints_matrix().ncols()
            1
        """
        return matrix(ZZ, 0, self.num_edges())

    def generators_matrix(self, mutable=None):
        r"""
        Return a basis of generators of x-coordinates as a matrix.

        As for a Strebel graph there is no constraints on coordinates, the
        answer is always the identity matrix.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: G = StrebelGraph("(0)(~0)")
            sage: G.generators_matrix()
            [1]
        """
        return identity_matrix(ZZ, self.num_edges())

    def add_residue_constraints(self, residue_constraints):
        r"""
        Return the Strebel graph linear family obtained by adding the given
        linear constraints on the residues.

        Note that the resulting linear family might not intersect the relative
        interior of the Strebel cone. To check whether this is the case, use
        the method ``is_core``.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: G = StrebelGraph("(0,2,~3,~1)(~0,3)(1)(~2)")

            sage: f1 = G.add_residue_constraints([[1, 0, 2, 0]])
            sage: f1
            StrebelGraphLinearFamily("(0,2,~3,~1)(~0,3)(1)(~2)", [(1, 0, 0, -1), (0, 1, 0, 1), (0, 0, 1, -1)])
            sage: f1.is_core()
            True

            sage: f2 = G.add_residue_constraints([[1, 0, 1, 0]])
            sage: f2
            StrebelGraphLinearFamily("(0,2,~3,~1)(~0,3)(1)(~2)", [(1, 0, 0, -1), (0, 1, 0, 0), (0, 0, 1, -1)])
            sage: f2.is_core()
            False

            sage: f3 = G.add_residue_constraints([[0, 1, -1, 0], [0, 1, 0, -1]])
            sage: f3
            StrebelGraphLinearFamily("(0,2,~3,~1)(~0,3)(1)(~2)", [(1, 0, 0, -1), (0, 1, 1, 1)])
            sage: f3.is_core()
            True
        """
        if not isinstance(residue_constraints, Matrix):
            residue_constraints = matrix(residue_constraints)

        gens = (residue_constraints * self.residue_matrix()).right_kernel_matrix()
        from .linear_family import StrebelGraphLinearFamily
        return StrebelGraphLinearFamily(self, gens)

    def delaunay_strebel_automaton(self, run=True, backend=None):
        r"""
        Return the Delaunay-Strebel automaton containing this Strebel graph.

        INPUT:

        - ``run`` -- optional boolean (default ``True``) -- whether to run the exploration
          of the automaton

        - ``backend`` -- an optional string -- a choice of backend for cone computations.
          A reasonable default choice is made based upon your installation and the base
          ring of the family.

        EXAMPLES::

            sage: from veerer import StrebelGraph

            sage: G = StrebelGraph("(0,1,2,3)")
            sage: G.delaunay_strebel_automaton()
            Delaunay-Strebel automaton with 327 states
        """
        from .automaton import DelaunayStrebelAutomaton
        A = DelaunayStrebelAutomaton(backward=True, backend=backend)
        A.add_seed(self)
        if run:
            A.run()
        return A

    def half_edge_num_separatrices(self, half_edge):
        r"""
        Return the number of separatrices in the corner of the half-edge

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: G = StrebelGraph("(0:1, 1:0, ~1:1, ~0:0)")
            sage: G.half_edge_num_separatrices(0)
            2
            sage: G.half_edge_num_separatrices(1)
            1
            sage: G.half_edge_num_separatrices(2)
            1
        """
        return self._excess[half_edge] + 1

    def vertex_angle(self, half_edge):
        r"""
        Return the angle of the vertex adjacent to ``half_edge``.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: sg = StrebelGraph("(0:1, 1:0)(~0:3, ~1:1)")
            sage: sg.vertex_angle(0)
            4
            sage: sg.vertex_angle(1)
            5
        """
        a = 0
        for h in perm_orbit(self._vp, half_edge):
            a = a + self._excess[h] + 1
        return a

    def face_angle(self, half_edge, check=True):
        r"""
        Return the angle of the face adjacent to ``half_edge``.

        EXAMPLES::

            sage: from veerer import StrebelGraph
            sage: G = StrebelGraph("(0:1, 1:0)(~0:2, ~1:1)")
            sage: G.face_angle(0)
            -1
            sage: G.face_angle(1)
            -3
        """
        if check:
            h = self._check_half_edge(half_edge)

        a = 0
        for h in perm_orbit(self._fp, half_edge):
            a = a - self._excess[h]
        return a

    def _normalization_face_separatrix(self, half_edge, angle):
        r"""
        EXAMPLES::

            sage: from veerer import *
            sage: G = StrebelGraph("(0:1, 1:0, ~1:1, ~0:0)")
            sage: G._normalization_face_separatrix(2, 0)
            (0, 0)
        """
        if self.face_angle(half_edge) == 0:
            return (min(perm_orbit(self._fp, half_edge)), angle)

        last_angle = self.half_edge_num_separatrices(half_edge) - 1 #the valid range is between 1 and the number of vertical separatrices 
        while angle == last_angle:
            half_edge = self.previous_in_face(half_edge)
            angle = 0
            last_angle = self.half_edge_num_separatrices(half_edge) - 1
        return (half_edge, angle)

    def _check_face_separatrix(self, half_edge, angle):
        half_edge = self._check_half_edge(half_edge)
        if not isinstance(angle, numbers.Integral):
            raise ValueError("invalid angle for separatrix")
        angle = int(angle)
        num_seps =  self.half_edge_num_separatrices(half_edge)
        if angle < 0 or angle >= num_seps:
            raise ValueError("angle (={}) out of range for separatrix at half_edge={}; must be >= 0 and <= {}".format(angle, half_edge, num_seps))
        return self._normalization_face_separatrix(half_edge, angle)
