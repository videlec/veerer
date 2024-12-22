r"""
Conversions from pyflatsurf and sage-flatsurf to veerer.
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


from array import array

from sage.matrix.constructor import matrix

from .constants import RED, BLUE
from .features import sage_flatsurf_feature, pyflatsurf_feature
from .triangulation import Triangulation
from .veering_triangulation import VeeringTriangulation
from .linear_family import VeeringTriangulationLinearFamily


def oriented_slope(a, rotate=1):
    r"""
    Return either ``(1, 1)``, ``(1, -1)``, ``(-1, 1)`` or ``(-1, -1)``.

    If ``rotate`` is set to ``1`` then consider the edge as if it was rotated counterclockwise
    infinitesimally (to make horizontal edges positive slopes and vertical edges negative
    slopes). If it is set to ``-1`` then the rotation is in clockwise direction. If it is
    set to ``0`` then return ``0`` on horizontal and vertical.

    EXAMPLES::

        sage: from veerer.flatsurf_conversion import oriented_slope
        sage: oriented_slope((1, 1))
        (1, 1)
        sage: oriented_slope((-1, 1))
        (-1, 1)
        sage: oriented_slope((-1, -1))
        (-1, -1)
        sage: oriented_slope((1, -1))
        (1, -1)

        sage: oriented_slope((1, 0))
        (1, 1)
        sage: oriented_slope((0, 1))
        (-1, 1)
        sage: oriented_slope((-1, 0))
        (-1, -1)
        sage: oriented_slope((0, -1))
        (1, -1)

        sage: oriented_slope((1, 0), rotate=-1)
        (1, -1)
        sage: oriented_slope((0, 1), rotate=-1)
        (1, 1)
        sage: oriented_slope((-1, 0), rotate=-1)
        (-1, 1)
        sage: oriented_slope((0, -1), rotate=-1)
        (-1, -1)

        sage: oriented_slope((1, 0), rotate=0)
        0
        sage: oriented_slope((0, 1), rotate=0)
        0
        sage: oriented_slope((-1, 0), rotate=0)
        0
        sage: oriented_slope((0, -1), rotate=0)
        0

        sage: oriented_slope((0, 0))
        Traceback (most recent call last):
        ...
        ValueError: zero vector
    """
    x, y = a
    if not x and not y:
        raise ValueError("zero vector")
    if (x > 0 and y > 0):
        return (1, 1)
    if (x < 0 and y < 0):
        return (-1, -1)
    if (x > 0 and y < 0):
        return (1, -1)
    if (x < 0 and y > 0):
        return (-1, 1)

    if rotate == 0:
        return 0
    if rotate == 1:
        if x > 0:
            return (1, 1)
        if y > 0:
            return (-1, 1)
        if x < 0:
            return (-1, -1)
        if y < 0 :
            return (1, -1)
    if rotate == -1:
        if x > 0:
            return (1, -1)
        if y > 0:
            return (1, 1)
        if x < 0:
            return (-1, 1)
        if y < 0:
            return (-1, -1)
    raise ValueError("invalid argument rotate={}".format(rotate))


def flat_structure_to_sage_flatsurf(flat_structure):
    r"""
    Construct a sage-flatsurf surface associated to the given veerer flat structure.

    Return a pair ``(surface, mapping_of_half_edges)``.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from veerer.flatsurf_conversion import flat_structure_to_sage_flatsurf

        sage: T = VeeringTriangulation("(0,1,2)(~0,~1,~2)", "BRR")
        sage: F = T.flat_structure_min()
        sage: flat_structure_to_sage_flatsurf(F)  # optional - sage_flatsurf
        (Translation Surface in H_1(0) built from 2 isosceles triangles,
         [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2)])

        sage: T = VeeringTriangulation("(0,1,2)", "BRR")
        sage: F = T.flat_structure_min()
        sage: flat_structure_to_sage_flatsurf(F)  # optional - sage_flatsurf
        (Half-Translation Surface in Q_0(-1^4) built from an isosceles triangle,
         [(0, 0), None, (0, 1), None, (0, 2), None])
    """
    sage_flatsurf_feature.require()
    import flatsurf

    ep = flat_structure._ep
    vp = flat_structure._vp
    bdry = flat_structure._bdry
    ne = flat_structure.num_edges()
    vecs = flat_structure.vectors()

    base_ring = flat_structure._x.base_ring()
    half_edge_to_face = [None] * (2 * ne)
    half_edge_to_pos = [None] * (2 * ne)
    S = flatsurf.MutableOrientedSimilaritySurface(base_ring)
    for i, t in enumerate(flat_structure.triangles()):
        for j, h in enumerate(t):
            half_edge_to_face[h] = i
            half_edge_to_pos[h] = j
        S.add_polygon(flatsurf.Polygon(edges=[vecs[t[0]], vecs[t[1]], vecs[t[2]]]))
    for e in range(ne):
        if not bdry[2 * e] and not bdry[ep(2 * e)]:
            S.glue((half_edge_to_face[2 * e], half_edge_to_pos[2 * e]),
                   (half_edge_to_face[ep(2 * e)], half_edge_to_pos[ep(2 * e)]))
    S.set_immutable()

    m = [None] * (2 * ne)
    for h in range(2 * ne):
        if vp[h] == -1:
            continue
        label = half_edge_to_face[h]
        e = half_edge_to_pos[h]
        m[h] = (label, e)
    return S, m


def pyflatsurf_surface_to_veerer_veering_triangulation(surface):
    r"""
    Convert a pyflatsurf surface in a veering triangulation.

    Note that the flat structure is lost in the process.

    EXAMPLES::

        sage: from veerer.flatsurf_conversion import pyflatsurf_surface_to_veerer_veering_triangulation

        sage: from flatsurf import Polygon, similarity_surfaces  # optional - sage_flatsurf pyflatsurf
        sage: P = Polygon(angles=(1,1,1,7), lengths=(3, 2))  # optional - sage_flatsurf pyflatsurf
        sage: S1 = similarity_surfaces.billiard(P).minimal_cover("translation").erase_marked_points()  # optional - sage_flatsurf pyflatsurf
        sage: S2 = S1.l_infinity_delaunay_triangulation()  # optional - sage_flatsurf pyflatsurf
        sage: S2.is_veering_triangulated()  # optional - sage_flatsurf pyflatsurf
        True
        sage: S3 = S2.pyflatsurf().codomain().flat_triangulation()  # optional - sage_flatsurf pyflatsurf
        sage: pyflatsurf_surface_to_veerer_veering_triangulation(S3)  # optional - sage_flatsurf pyflatsurf
        (VeeringTriangulation("(0,1,2)(~0,3,4)(~1,5,6)(~2,7,8)(~3,10,9)(~4,11,~8)(~5,12,13)(~6,14,15)(~7,~9,~14)(~10,16,~11)(~12,17,18)(~13,19,20)(~15,~18,~20)(~16,~17,~19)", "BRRRRRBRBBBRBRRRRRBBR"),
        [-1, -1, ..., -1])
    """
    pyflatsurf_feature.require()

    faces = surface.faces()
    n = 3 * faces.size()
    fp = array('i', [-1] * n)
    slopes = [-1] * (n // 2)
    orientations = [None] * (n // 2)
    for face in faces:
        a, b, c = face
        va = surface.fromHalfEdge(a)
        sa = oriented_slope((va.x(), va.y()))
        vb = surface.fromHalfEdge(b)
        sb = oriented_slope((vb.x(), vb.y()))
        vc = surface.fromHalfEdge(c)
        sc = oriented_slope((vc.x(), vc.y()))
        a = a.id()
        b = b.id()
        c = c.id()
        if a < 0 :
            a = 2 * (-a - 1) + 1
        elif a > 0:
            a = 2 * (a - 1)
        if b < 0:
            b = 2 * (-b - 1) + 1
        elif b > 0:
            b = 2 * (b - 1)
        if c < 0:
            c = 2 * (-c - 1) + 1
        elif c > 0:
            c = 2 * (c - 1)
        fp[a] = b
        fp[b] = c
        fp[c] = a
        if a % 2:
            orientations[a // 2] = -sa[0]
        else:
            orientations[a // 2] = sa[0]
        slopes[a // 2] = sa[0] * sa[1]
        if b % 2:
            orientations[b // 2] = -sb[0]
        else:
            orientations[b // 2] = sb[0]
        slopes[b // 2] = sb[0] * sb[1]
        if c % 2:
            orientations[c // 2] = -sc[0]
        else:
            orientations[c // 2] = sc[0]
        slopes[c // 2] = sc[0] * sc[1]

    colouring = array('i', [RED if x == 1 else BLUE for x in slopes])
    return VeeringTriangulation.from_permutations(None, fp, (array('i', [0] * n),), (colouring,)), orientations 


def sage_flatsurf_orbit_closure_to_veerer_linear_family(orbit_closure):
    r"""
    Conversion of sage-flatsurf ``GL2ROrbitClosure`` to veerer ``VeeringTriangulationLinearFamily``.

    EXAMPLES::

        sage: from veerer.flatsurf_conversion import sage_flatsurf_orbit_closure_to_veerer_linear_family

        sage: from flatsurf import Polygon, similarity_surfaces, GL2ROrbitClosure  # optional - sage_flatsurf pyflatsurf
        sage: P = Polygon(angles=(1,1,1,7), lengths=(3, 2))  # optional - sage_flatsurf pyflatsurf
        sage: S1 = similarity_surfaces.billiard(P).minimal_cover("translation").erase_marked_points()  # optional - sage_flatsurf pyflatsurf
        sage: S2 = S1.l_infinity_delaunay_triangulation()  # optional - sage_flatsurf pyflatsurf
        sage: O = GL2ROrbitClosure(S2)  # optional - sage_flatsurf pyflatsurf
        sage: for d in O.decompositions(4):  # optional - sage_flatsurf pyflatsurf
        ....:     O.update_tangent_space_from_flow_decomposition(d)
        ....:     if O.dimension() == 4:
        ....:         break
        sage: F = sage_flatsurf_orbit_closure_to_veerer_linear_family(O)  # optional - sage_flatsurf pyflatsurf
        sage: F.base_ring()  # optional - sage_flatsurf pyflatsurf
        Number Field in c0 with defining polynomial x^2 - x - 1 with c0 = 1.618033988749895?
        sage: F  # optional - sage_flatsurf pyflatsurf
        VeeringTriangulationLinearFamily("(0,1,2)(~0,3,4)(~1,5,6)(~2,7,8)(~3,10,9)(~4,11,~8)(~5,12,13)(~6,14,15)(~7,~9,~14)(~10,16,~11)(~12,17,18)(~13,19,20)(~15,~18,~20)(~16,~17,~19)", "BRRRRRBRBBBRBRRRRRBBR", [(1, 0, 1, 0, 1, c0, c0, 0, -1, -c0, -c0, 0, c0, 0, c0, 2*c0, c0, 0, c0, -c0, c0), (0, 1, 1, 0, 0, c0, c0 - 1, 0, -1, -1, -1, -1, 1, c0 - 1, 1, c0, 0, -c0 + 1, -c0 + 2, -c0 + 1, 2*c0 - 2), (0, 0, 0, 1, 1, 0, 0, 0, 0, -c0, -c0 + 1, 1, 0, 0, c0, c0, c0, c0 - 1, c0 - 1, -1, 1), (0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, c0 - 1, c0 - 1, c0 - 1, -c0 + 1)])
    """
    sage_flatsurf_feature.require()

    vt, orientations = pyflatsurf_surface_to_veerer_veering_triangulation(orbit_closure._surface)

    # build generators for the tangent space
    phi = orbit_closure.V2.base_ring().coerce_embedding()
    K = phi.codomain()
    subspace = []
    for i in range(orbit_closure._U_rank):
        v = orbit_closure.lift(orbit_closure._U[i])
        v = [orientations[j] * phi(v[j]) for j in range(len(v))]
        subspace.append(v)

    R = orbit_closure.field_of_definition()
    if orbit_closure.base_ring() != R:
        subspace = matrix(orbit_closure.base_ring(), subspace).echelon_form().change_ring(R)
    return VeeringTriangulationLinearFamily(vt, subspace)
