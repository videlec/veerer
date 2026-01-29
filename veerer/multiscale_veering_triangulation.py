r"""
Multi-scale Veering Triangulations
"""

# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024-2025 Vincent Delecroix
#                     2024-2025 Kai Fu
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

from sage.structure.richcmp import op_LT, op_GT, op_LE, op_GE, rich_to_bool
from sage.structure.element import Matrix
from sage.rings.integer_ring import ZZ
from sage.matrix.constructor import matrix
from sage.matrix.special import identity_matrix

from .permutation import perm_check, perm_cycles, perm_cycles_to_string, str_to_cycles, str_to_cycles_and_data, perm_init, perm_invert
from .triangulation import Triangulation
from .veering_triangulation import *
from .constants import *
from .polyhedron import *
from .labelled_digraph import *
from .monodromy import *

def str_to_label(h):
    r"""
    Turn a string into the label of the half-edge
    """
    if h[0] == '~':
        lh = 2*int(h[1:]) + 1
    else:
        lh = 2*int(h[0:])
    return lh

def in_connected_component(vt, h):
    r"""
    Return the index of the component which contains the half-edge h in the list vt.connected_components()
    """
    l_comp = vt.connected_components()
    for comp in l_comp:
        if (h // 2) in comp:
            return l_comp.index(comp)

def track_prong(vt, r_up, r_low, prong, vertex=False, face=False):
    r"""
    Return the prong after the vertival degeneration (without normalization).

    Note that r_up and r_low are from the method VeeringTriangulation.degeneration by setting `collapsed_half_edge_relabelling=True`.

    EXAMPLES::

        sage: from veerer import *
        sage: from veerer.multiscale_veering_triangulation import track_prong

        sage: vt = VeeringTriangulation("(0,1,2)(~1,~5,~0)(~2,3,4)(5,~3,~4)","RRBBRB")
        sage: edges_low = [4]
        sage: _, f_low, r_up, r_low = vt.degeneration(edges_low=edges_low, collapsed_half_edge_relabelling=True)
        sage: prong1 = (0, 0, 1, 0)
        sage: prong2 = (0, 0, 9, 0)
        sage: track_prong(vt, r_up, r_low, prong1, vertex=True)
        (1, 0, 0, 1)
        sage: track_prong(vt, r_up, r_low, prong2, vertex=True)
        (1, 0, 1, 0)

        sage: vt = VeeringTriangulation("(0,1,2)(~0:1,~2:1,~1:2)", "BRR")
        sage: edges_low = [0]
        sage: _, _, r_up, r_low = vt.degeneration(edges_low=edges_low, collapsed_half_edge_relabelling=True)
        sage: prong = (0, 0, 5, 0)
        sage: track_prong(vt, r_up, r_low, prong, vertex=True)
        (1, 0, 0, 0)
        sage: track_prong(vt, r_up, r_low, prong, face=True)
        (0, 0, 1, 0)

        sage: vt = VeeringTriangulation("(~0,~2,~3)(~1,2,3)(0:4,1:4)", "BBRR")
        sage: edges_up = [2, 3]
        sage: _, _, r_up, r_low = vt.degeneration(edges_up=edges_up, collapsed_half_edge_relabelling=True)
        sage: prong = (1, 3, 2, 1)
        sage: track_prong(vt, r_up, r_low, prong, face=True)
        (1, 3, 2, 1)

        sage: vt = VeeringTriangulation("(0:1,1:2,~0:1,~1:4)(2:1,3:2,~2:1,~3:4)", "RRRR")
        sage: _, _, r_up, r_low = vt.degeneration(edges_low=(1, 3), edges_up=(0, 2), collapsed_half_edge_relabelling=True)
        sage: track_prong(vt, r_up, r_low, (1, 0, 7, 2), face=True)
        (1, 0, 2, 2)

        sage: vt = VeeringTriangulationLinearFamily("(0:1,1:1,2:1)(~0:1,~1:1,~2:1)", "RRR", [(1, 0, 0), (0, 1, 0), (0, 0, 1)])
        sage: _, _, r_up, r_low = vt.degeneration(edges_low=(0,), collapsed_half_edge_relabelling=True)
        sage: track_prong(vt, r_up, r_low, (0, 0, 1, 0), face=True)
        (0, 0, 1, 0)
    """
    l, c, h, ang = prong
    l = abs(l)

    if vertex:
        vt._check_vertex_separatrix(h, ang)
        vh = [r_up[e] for e in perm_orbit(vt._vp, h)]
        if min(vh) >= 0: # The vertex of h is contaiend in f_up
            return (l, c, r_up[h], ang)

        # Otherwise the vertex prong must be contained in f_low
        a = 0
        while r_up[h] >= 0:
            h = vt.previous_at_vertex(h)
            b = vt.half_edge_num_separatrices(h)
            a = a + b
        ang = ang + a
        assert r_low[h] >= 0
        return (l + 1, 0, r_low[h], ang) if max(r_up) >=0 else (l, c, r_low[h], ang) # Note that the degeneration might be horizontal

    elif face:
        vt._check_face_separatrix(h, ang)
        assert vt.boundary_vector()[h] > 0
        fh = [r_low[e] for e in perm_orbit(vt._fp, h)]
        if min(fh) >= 0: #The pole of h is contaiend in f_low
            return (l + 1, 0, r_low[h], ang) if max(r_up) >=0 else (l, c, r_low[h], ang)

        # Otherwise the face prong must be contained in f_up
        a = 0
        while r_low[h] >= 0:
            h = vt.next_in_face(h)
            b = vt.half_edge_num_separatrices(h)
            a = a + b - 1
        ang = ang + a
        assert r_up[h] >= 0
        return (l, c, r_up[h], ang)

    else:
        return ValueError("Missing argument of 'vertex' or 'face'.")

def _vaninshing_red_blue_corner(vt, r_up, r_low, h):
    hh = vt.next_at_vertex(h)
    if r_up[h] >= 0 and r_low[hh] >= 0 and vt.boundary_vector()[h] == 0 and vt.half_edge_num_separatrices(h) == 1:
        return True
    else:
        return False

def new_prong_matching(vt, f_low, r_up, r_low, level, comp):
    r"""
    Return the new vertical node indecued by the vertical degeneration of the veering triangulation.

    Note that r_up and r_low are from the method VeeringTriangulation.degeneration by setting `collapsed_half_edge_relabelling=True`.

    EXAMPLES::

        sage: from veerer import *
        sage: from veerer.multiscale_veering_triangulation import new_prong_matching

        sage: vt = VeeringTriangulation("(0,1,2)(~1,~5,~0)(~2,3,4)(5,~3,~4)","RRBBRB")
        sage: edges_low = [4]
        sage: _, f_low, r_up, r_low = vt.degeneration(edges_low=edges_low, collapsed_half_edge_relabelling=True)
        sage: new_prong_matching(vt, f_low, r_up, r_low, 0, 0)
        [[(0, 0, 0, 0), (1, 0, 1, 1)]]
    """
    level = abs(level)
    nh = 2 * vt.num_edges()
    newpm = []
    lpoles = [] #the poles at nodes in f_low considered so far
    for h in range(nh):
        hh = vt.next_at_vertex(h)
        if (r_up[h] >= 0) and (r_low[hh] >= 0):
            #find the boundary face in f_low containing hh
            for f in f_low.boundary_faces():
                if f_low.next_in_edge(r_low[hh]) in f:
                    f_pole = f

            if f_pole not in lpoles:
                while ((vt.half_edge_num_separatrices(h) == 0) and (r_up[h] >= 0)) or (_vaninshing_red_blue_corner(vt, r_up, r_low, h)):
                    h = vt.previous_at_vertex(h)
                if (vt.half_edge_num_separatrices(h) > 0) and (r_up[h] >= 0):
                    vert_sep = (level, comp, h, 0)
                    prong1 = (level,comp, r_up[h], 0)
                    prong2 = track_prong(vt, r_up, r_low, vert_sep, vertex=True) # This prong is obtained by tracing the vertex prong after the vertical degeneration.
                    assert prong2[0] == level + 1
                    pm = [prong1, prong2]
                    newpm.append(pm)
                    lpoles.append(f_pole)
    return newpm

class NodalLabelledDiGraph(LabelledDiGraph):
    r"""
    Graph encoding the level structure of a multiscale veering triangulation.

    The vertices are pairs of integers ``(level, prime_component_number)`` that are in bijection with the connected
    components of the multiscale veering triangulations. The edges represent
    the nodes and could either be between two components in the same
    level (horizontal nodes) or from a component in some level to some
    component in a lower level (vertical nodes).

    EXAMPLES::

        sage: from veerer.multiscale_veering_triangulation import NodalLabelledDiGraph

        sage: N = NodalLabelledDiGraph([1, 1, 2], [(0, 0, 7, 8), (1, 0, 3, 5), (1, 0, 2, 4)],
        ....:                      [((0, 0, 3, 3), (2, 1, 2, 2)),
        ....:                       ((1, 0, 5, 2), (2, 0, 3, 7)),
        ....:                       ((0, 0, 2, 6), (2, 0, 3, 2))],
        ....:                       [])
        sage: N
        Multiscale veering triangulation nodal graph with 3 horizontal and 3 vertical nodes

        sage: list(N.vertices(0))  # vertices at level 0
        [0]
        sage: list(N.vertices(1))  # vertices at level -1
        [1]
        sage: list(N.vertices(2))  # vertices at level -2
        [2, 3]

        sage: list(N.vertices(2, 0))  # vertices in the first prime component at level -2
        [2]
        sage: list(N.vertices(2, 1))  # vertices in the second prime component at level -2
        [3]
    """
    def __init__(self, prime_decomposition, horizontal_nodes, vertical_nodes, data_genus):
        r"""
        INPUT:

        - ``prime_decomposition`` -- a list of integers. The i-th list
          ``prime_decomposition[i]`` encodes the i-th level of the level graph
          and the number of prime components in this level.  The
          integer at position ``prime_connected_decomposition[i]`` is the
          number of prime components in the i-th level.

        - ``horizontal_nodes`` -- a list of horizontal node data ``(l, pc, h1, h2)``

        - ``vertical_nodes`` -- a list of vertical node data ``((l1, pc1, h1, a1), (l2, pc2, h2, a2))``
        """

        digraph = DiGraph(loops=True, multiedges=True)
        digraph.add_vertices([(l, pc)
                              for l, num_pc in enumerate(prime_decomposition)
                              for pc in range(num_pc)])

        # Add horizontal edges
        for l, pc, h1, h2 in horizontal_nodes:
            v = (l, pc)
            if not (0 <= l < len(prime_decomposition) and
                    0 <= pc < prime_decomposition[l]):
                raise ValueError(f"invalid horizontal node between ({l}, {pc}) and ({l}, {pc})")
            if h2 <= h1:
                raise ValueError(f"invalid normalization of half-edges for horizontal node; got h1={h1} and h2={h2}")
            digraph.add_edge(v, v, (h1, h2))

        # Add vertical edges
        for p1, p2 in vertical_nodes:
            l1, pc1, h1, ang1 = p1
            l2, pc2, h2, ang2 = p2
            if not (0 <= l1 < l2 < len(prime_decomposition) and
                    0 <= pc1 < prime_decomposition[l1] and
                    0 <= pc2 < prime_decomposition[l2]):
                raise ValueError(f"invalid vertical node between (l={l1}, pc={pc1}) and (l={l2}, pc={pc2})")
            v1 = (l1, pc1)
            v2 = (l2, pc2)
            digraph.add_edge(v1, v2, (h1, ang1, h2, ang2))

        # TODO: Should we allow disconnected level graphs?
        if not digraph.is_connected():
            raise ValueError("disconnected level graph")

        super().__init__(digraph)

        self._data_genus = data_genus

    def copy(self):
        ans = LabelledDiGraph.copy(self)
        return ans

    def __repr__(self):
        return "Multiscale veering triangulation nodal graph with {} horizontal and {} vertical nodes".format(sum(self.vertex_level(self.edge_source(e)) == self.vertex_level(self.edge_target(e)) for e in range(self.num_edges())), sum(self.vertex_level(self.edge_source(e)) != self.vertex_level(self.edge_target(e)) for e in range(self.num_edges())))

    def vertex_level(self, vertex):
        return self._vertices[vertex][0]

    def vertices(self, level=None, prime_component=None):
        r"""
        Iterate through vertices.

        If a ``level`` is provided, only return the vertices in a given level. If both
        ``level`` and ``prime_component`` are provided, return the vertex
        corresponding to a given prime component.
        """
        if level is None:
            if prime_component is not None:
                raise ValueError("invalid input")
            return range(self.num_verts())
        elif prime_component is None:
            for v, label in enumerate(self._vertices):
                if label[0] == level:
                    yield v
        else:
            yield self._vertex_index[(level, prime_component)]

    def level_graph(self, mvt):
            r"""
            Return the underlying level graph of the multi-scale veering triangulation as a labelled digraph.
            """
            vts = mvt._veering_triangulations
            digraph = DiGraph(loops=True, multiedges=True)
            digraph.add_vertices([(l, pc, cc)
                                for l, pc in self._vertices
                                for cc in range(len(vts[l][pc].connected_components()))])
            for e, label in enumerate(self._edges):
                l1, pc1 = self._vertices[self.edge_source(e)]
                l2, pc2 = self._vertices[self.edge_target(e)]
                if len(label) == 2:
                    assert (l1, pc1) == (l2, pc2)
                    vt = vts[l1][pc1]
                    h1, h2 = label
                    cc1 = in_connected_component(vt,h1)
                    cc2= in_connected_component(vt, h2)
                elif len(label) == 4:
                    h1, _, h2, _ = label
                    vt1 = vts[l1][pc1]
                    vt2 = vts[l2][pc2]
                    cc1 = in_connected_component(vt1,h1)
                    cc2 = in_connected_component(vt2,h2)
                v1 = (l1, pc1, cc1)
                v2 = (l2, pc2, cc2)
                digraph.add_edge(v1, v2, label)
            return LabelledDiGraph(digraph)

    # TODO: do we really need to compute edges here? In other words, is it
    # fine to just return self._digraph.subgraph(vertices=vertices)?
    def subgraph_above_level(self, mvt, level):
        r"""
        Return the subgraph of the level graph of ``mvt`` induced on vertices with level above ``level``.
        """
        level_g = self.level_graph(mvt)
        vertices = [i for i, v in enumerate(level_g._vertices) if v[0] < level]
        return level_g._digraph.subgraph(vertices=vertices)

    def vertical_edges_for_GRC(self, mvt, level):
        r"""
        Return a list of dictionary for later check of global residue conditions.

        The key `v` of each dictionary is a vertex at the `level`-th level of the nodal graph.
        The value of key `v` consists of the edges from the same component of the subgraph above
        level-`level` to the vertices in the prime component of `v`. Note the the indices of the
        edges refer to the indices in the level graph.

        EXAMPLES::

            sage: from veerer import *

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[VeeringTriangulationLinearFamily("(0:1)(~0:1)(1:1)(~1:1)(2:1)(~2:1)(3:1)(~3:1)", "RRRR", [(1, 1, 1, 1)])],[VeeringTriangulationLinearFamily("(0:3)(~0:3)(1:3)(~1:3)", "RR", [(1, 1)])]],horizontal_nodes=[[[(0, 2), (1, 4), (3, 5), (6, 7)]], [[]]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 1)), ((0, 0, 4, 0), (1, 0, 3, 1))])
            sage: g = mvt._nodal_digraph
            sage: g.vertical_edges_for_GRC(mvt, 1)
            [defaultdict(<class 'list'>, {1: [2, 4]}), defaultdict(<class 'list'>, {})]
        """
        level_g = self.level_graph(mvt)
        subd = self.subgraph_above_level(mvt, level)
        components = subd.connected_components(sort=False)
        edges = []
        ne = self.num_edges()
        for comp in components:
            l = [e for e in range(ne) if (level_g.edge_source(e) in comp) and (level_g._vertices[level_g.edge_target(e)][0] == level)]
            # divide the list `l1` according to the edge targets in the nodal graph.
            targets = []
            for e in l:
                lvl, c,_ = level_g._vertices[level_g.edge_target(e)]
                targets.append(self.vertex_index((lvl,c)))
            from collections import defaultdict
            dic_groups = defaultdict(list)
            for index, v in enumerate(targets):
                dic_groups[v].append(l[index])
            edges.append(dic_groups)
        return edges
    
    def is_stable_without_markings(self, v):
        """
        Return True if the vertex is stable when the zeros and poles are forgetten.
        """
        dg = self._digraph
        n = dg.degree(v)
        genus = self._data_genus[v]
        return 2 - 2*genus - n < 0

class MultiscaleVeeringTriangulation:
    r"""
    Multi-scale Veering Triangulations.

    A *multi-scale veering triangulation* is a triangulation of a (nodal) surface such that the restriction to each irreducible component forms a veering triangulation. Additionally, it encodes the information at the nodes.

    INPUT:

    veering_triangulation : a list of length N, where the i-th entry is a list of veering triangulations

    horizontal_nodes : a list of length N, where the i-th entry is a list [l0, l1, ...], satisfying that:
    - lj encodes the horizontal nodes at the j-th component of the level-i veering triangulations,
    - the horizontal nodes in each lj is of the form
    "[h1, h2]"
    , where the half-edges h1 and h2 are contained in the boundary face of simple poles.

    prong_matching : a list consistings of pairs (prong1,prong2) with
    prong1 = (level1, label1, h1, angle1)
    prong2 = (level2, label2, h2, angle2)
    where:
    - level1 > level2
    - h1 is an half-edge at a zero of the veering triangulation 'vt1' at level1, and h2 is an hal-edge in a boundary face of the veering triangulation 'vt2' at level2
    - angle1 and angle2 are the indices of the vertical separatrices in the corner of h1 and h2 respectively satisfying that:
    the angle1 is in [0, vt1.half_edge_num_separatrices(h1)],
    and the angle2 is in [0, vt2.half_edge_num_separatrices(h2)].

    EXAMPLES::

        sage: from veerer import VeeringTriangulation, MultiscaleVeeringTriangulation

    An example with non-trivial glabal residue condition::

        sage: vt = VeeringTriangulation("(0,1,2)(4,~2,3)(~3,5,6)(~6,~0,~1)(11, 12,~10)(8,9,10)(~13, 7, ~9)(13,~11,~12)(~5,~7,14)(~14,~4,~8)", "RBBBRRBBBRRBRRB")
        sage: vt.stratum()  # optional - surface dynamics
        H_3(4)
        sage: vt.is_delaunay()
        True
        sage: edges_low = [4,5,7,8,14]
        sage: mvt = MultiscaleVeeringTriangulation([vt])
        sage: mvt1 = mvt.degeneration(0, 0, edges_low=edges_low)
        sage: mvt1
        MultiscaleVeeringTriangulation(
        veering_triangulations=[
        [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)])],
        [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
        ],
        horizontal_nodes=[[[]], [[]]],
        prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 10, 0), (1, 0, 4, 0))]
        )
        sage: vt0 = mvt1._veering_triangulations[0][0]
        sage: vt1 = mvt1._veering_triangulations[1][0]
        sage: vt0.stratum()  # optional - surface dynamics
        (H_1(0), H_1(0))
        sage: vt1.stratum()  # optional - surface dynamics
        H_1(4, -2^2)
        sage: vt1.residue_constraints()
        [1 0]
        [0 1]
        sage: mvt1.ambient_stratum()  # optional - surface dynamics
        H_3(4)
    """

    def __init__(self, veering_triangulations=None, horizontal_nodes=None, prong_matchings=None, mutable=False, check=True):
        if isinstance(veering_triangulations, list):
            self._veering_triangulations = []
            prime_decomposition = [] # data for building the vertices of nodal digraph
            data_genus = [] # data of genus information of the vertices of nodal digraph
            for level, vts in enumerate(veering_triangulations):
                if isinstance(vts, VeeringTriangulation):
                    vts = [vts]     
                if isinstance(vts, list):
                    self._veering_triangulations.append([])
                    for vt in vts:
                        if not isinstance(vt, VeeringTriangulation):
                            raise TypeError(f"input must be veering triangulations; got {type(vt).__name__}")
                        # compute the genus of vt
                        if vt.is_connected():
                            g = vt.genus()
                        else:
                            g = sum(c.genus() for _, c in vt.connected_components_subgraphs())
                        data_genus.append(g)
                        self._veering_triangulations[-1].append(vt)
                    #self._veering_triangulations.append(list(vts))
                    prime_decomposition.append(len(vts))
                else:
                    raise ValueError(f"invalid list of veering triangulations {vts} at level-{level}")
        else:
            raise ValueError("The 'veering_triangulations' must be a list.")

        if isinstance(horizontal_nodes, list):
            if len(horizontal_nodes) != len(self._veering_triangulations):
                raise ValueError("veering_triangulations and horizontal_nodes must have the same length; got {len(veering_triangulations)} and {len(horizontal_nodes)}")
            data_horiz_nodes = [] # data for building nodal digraph
            for level in range(len(horizontal_nodes)):
                nodes = horizontal_nodes[level]
                vts = self._veering_triangulations[level]
                if len(nodes) != len(vts):
                    raise ValueError(f"veering_triangulations[{level}] and horizontal_nodes[{level}] must have the same length; got {len(vts)} and {len(nodes)}")
                for c in range(len(vts)):
                    nodes_at_c = []
                    vt = vts[c]
                    if isinstance(nodes[c], (tuple, list)):
                        if all(isinstance(n, (tuple, list)) and len(n) == 2 and isinstance(n[0], numbers.Integral) and isinstance(n[1], numbers.Integral) for n in nodes[c]):
                            nodes_at_c = [(int(n[0]), int(n[1])) for n in nodes[c]]
                        else:
                            raise ValueError(f"invalid input {nodes[c]} to specify horizontal nodes in a given prime component; it must be a list of pairs")
                    elif isinstance(nodes[c], str):
                        nodes_at_c = str_to_cycles(nodes[c])
                        for i, node in enumerate(nodes_at_c):
                            for j in range(2):
                                h = node[j]
                                if h < 0:
                                    h = -2 * h - 1
                                else:
                                    h = 2 * h
                                node[j] = vt._check_half_edge(h)
                            nodes_at_c[i] = tuple(node)
                    else:
                        raise ValueError(f"invalid horizontal node specification; got a {type(nodes[c]).__name__} at the {c}-th component of level-{level} instead of a list of pairs of half-edges")

                    # normalization of horizontal nodes
                    fp = vt.face_permutation()
                    for node in nodes_at_c:
                        h1, h2 = node
                        h1 = min(perm_orbit(fp, h1))
                        h2 = min(perm_orbit(fp, h2))
                        h1, h2 = sorted([h1, h2])
                        if check:
                            self._check_horizontal_node(level, c, (h1, h2))
                        data_horiz_nodes.append((level, c, h1, h2))
                    data_horiz_nodes = sorted(data_horiz_nodes)
        elif horizontal_nodes is None:
            data_horiz_nodes = []
        else:
            raise TypeError("The 'horizontal_nodes' must be a list; got {}".format(type(horizontal_nodes).__name__))

        if isinstance(prong_matchings, list):
            data_vert_nodes = [] # data for building nodal digraph
            for pm in prong_matchings:
                pm = self._normalize_prong_matching(pm)
                if check:
                    self._check_local_prong_matching(pm)
                data_vert_nodes.append(pm)
            data_vert_nodes = sorted(data_vert_nodes)
        elif prong_matchings is None:
            data_vert_nodes = []
        else:
            raise ValueError("The 'prong_matchings' must be a list.")

        self._nodal_digraph = NodalLabelledDiGraph(prime_decomposition, data_horiz_nodes,data_vert_nodes, data_genus) # build the nodal digraph. Note that the order of the loops in the digraph are inverted?

        self._mutable = True
        if not mutable:
            self.set_immutable()

        if check:
            self._check()

    def _horizontal_nodes(self, sort=False):
        r"""
        Return horizontal nodes as a list of list
        """
        g = self._nodal_digraph
        N = self.num_levels()

        l = [[[] for _ in range(len(self._veering_triangulations[level]))] for level in range(N)]

        for e, label in enumerate(g._edges):
            if len(label) == 2:
                level, c = g.vertex_label(g.edge_source(e))
                l[level][c].append(label)

        if sort:
            for level in range(N):
                for c in range(len(l[level])):
                    l[level][c].sort()
        return l

    def _normalize_prong_matching(self, pm):
        (l1, c1, h1, a1), (l2, c2, h2, a2) = pm
        l1 = self._check_level(l1)
        c1 = self._check_component(l1, c1)
        l2 = self._check_level(l2)
        c2 = self._check_component(l2, c2)
        if l2 <= l1:
            raise ValueError(f"invalid prong matching; got l1={l1} and l2={l2}")
        vt1 = self._veering_triangulations[l1][c1]
        vt2 = self._veering_triangulations[l2][c2]
        h1, a1 = vt1._check_vertex_separatrix(h1, a1)
        h2, a2 = vt2._check_face_separatrix(h2, a2)
        h2, a2 = vt2._normalize_face_separatrix(h2, a2)
        for (hh1, aa1), (hh2, aa2) in zip(vt1.vertex_separatrices(h1, a1), vt2.face_separatrices(h2, a2)):
            if (hh1, aa1) < (h1, a1):
                h1 = hh1
                a1 = aa1
                h2 = hh2
                a2 = aa2
        assert a1 == 0
        return ((l1, c1, h1, a1), (l2, c2, h2, a2))

    def _prong_matchings(self, sort=False):
        g = self._nodal_digraph
        l = []
        for e, label in enumerate(g._edges):
            if len(label) == 4:
                h1, ang1, h2, ang2 = label
                level1, c1 = g.vertex_label(g.edge_source(e))
                level2, c2 = g.vertex_label(g.edge_target(e))
                l.append(((level1, c1, h1, ang1), (level2, c2, h2, ang2)))
        if sort:
            l.sort()
        return l

    def _check(self):
        NG = self._nodal_digraph
        for e in range(NG.num_edges()):
            u = NG._edge_sources[e]
            v = NG._edge_targets[e]
            if u == v:
                # horizontal edge
                level, comp = NG._vertices[u]
                (h0, h1) = NG._edges[e]
                if h0 != self._veering_triangulations[level][comp]._check_infinite_cylinder(h0):
                    raise ValueError(f"non-normalized half-edge h0={h0} in horizontal node")
                if h1 != self._veering_triangulations[level][comp]._check_infinite_cylinder(h1):
                    raise ValueError(f"non-normalized half-edge h1={h1} in horizontal node")
            else:
                # vertical edge
                level0, comp0 = NG._vertices[u]
                level1, comp1 = NG._vertices[v]
                if level0 >= level1:
                    raise ValueError("invalid vertical node orientation in the nodal di-graph")
                (h0, a0, h1, a1) = NG._edges[e]
                if (h0, a0) != self._veering_triangulations[level0][comp0]._check_vertex_separatrix(h0, a0):
                    raise ValueError(f"non-normalized vertex separatrix (h0, a0)=({h0}, {a0}) in vertical node")
                if ((h1, a1) != self._veering_triangulations[level1][comp1]._check_face_separatrix(h1, a1) or
                    (h1, a1) != self._veering_triangulations[level1][comp1]._normalize_face_separatrix(h1, a1)):
                    raise ValueError(f"non-normalized face separatrix (h1, a1)=({h1}, {a1}) in vertical node")

        self._check_horizontal_residue_conditions()
        self._check_prong_matching()
        self._check_global_residue_conditions()

    def _check_level(self, level):
        r"""
        Return a level as a positive integer
        """
        if not isinstance(level, numbers.Integral):
            raise TypeError("level must be integral; got {}".format(type(level).__name__))
        level = int(level)
        if level < 0:
            level = -level
        if not 0 <= level < self.num_levels():
            raise ValueError("level out of range")
        return level

    def _check_component(self, level, component):
        level = self._check_level(level)
        if not isinstance(component, numbers.Integral):
            raise TypeError("component must be integral; got {}".format(type(component).__name__))
        component = int(component)
        if not 0 <= component < len(self._veering_triangulations[level]):
            raise ValueError("component out of range")
        return component

    def _check_horizontal_node(self, level, c, node):

        level = self._check_level(level)

        h1, h2 = node
        vt = self._veering_triangulations[abs(level)][c]

        if (vt.face_angle(h1) != 0):
            raise ValueError(f"The half-edge {h1} of {c}-th component at level-{level} is not in the face of simple pole")
        elif (vt.face_angle(h2) != 0):
            raise ValueError(f"The half-edge {h2} of {c}-th component at level-{level} is not in the face of simple pole")

        f0, f1 = self.horizontal_faces(level, c, node)
        if f0 == f1:
            raise ValueError(f"The half-edge {h1} and {h2} are in the same face of simple pole")
        for hh in f0:
            for hhh in f1:
                if vt._colouring[hh // 2] != vt._colouring[hhh // 2]:
                    raise ValueError(f"The boundary edges in the face of {h1} and the face of {h2} have different colors")

    def _check_horizontal_residue_conditions(self):
        for level, nodes in enumerate(self._horizontal_nodes()):
            for c, nodes_at_c in enumerate(nodes):
                for h1, h2 in nodes_at_c:
                    vt = self._veering_triangulations[level][c]
                    v1 = vector(vt.base_ring(), vt.num_edges())
                    for h in perm_orbit(vt._fp, h1):
                        v1[h // 2] += 1
                    v2 = vector(vt.base_ring(), vt.num_edges())
                    for h in perm_orbit(vt._fp, h2):
                        v2[h // 2] += 1

                    gens = vt.generators_matrix()
                    gv1 = gens * v1
                    gv2 = gens * v2
                    if gv1 != gv2 and gv1 != -gv2:
                        raise ValueError(f"distinct residues at horizontal node {(h1, h2)} at the {c}-th component at level {level}")

    def _check_local_prong_matching(self, pm):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation, MultiscaleVeeringTriangulation

            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: pm = ((0, 0, 0,4),(-1, 0, 0, 1))
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: angle (=4) out of range for separatrix at half_edge=0; must be >= 0 and < 4
            sage: pm = ((0,0,7,0),(1,0,0,1))
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: angle (=0) out of range for separatrix at half_edge=7; must be >= 0 and < 0
            sage: pm = ((0,0,1,0),(1,0,0,1))
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: The orders of the zero in (0, 0, 1, 0) and the pole in (1, 0, 0, 1) are not matched
        """
        N = len(self._veering_triangulations)
        prong1, prong2= pm

        l1, c1, h1, a1 = prong1
        l2, c2, h2, a2 = prong2

        vt1 = self._veering_triangulations[l1][c1]
        vt2 = self._veering_triangulations[l2][c2]

        #check the orders of the zero and pole are matched
        if vt2.face_angle(h2) == 0:
            raise ValueError(f"The prong {prong2} is contained in a face of simple pole")
        if (vt1.vertex_angle(h1) + vt2.face_angle(h2) != 0):
            raise ValueError(f"The orders of the zero in {prong1} and the pole in {prong2} are not matched")

        alpha1 = vt1.boundary_vector()
        alpha2 = vt2.boundary_vector()
        col1 = vt1._colouring

        hh1 = vt1.vertex_permutation()[h1]

        #check prong1
        if (alpha1[h1] == 0) and (a1 != 0):
            raise ValueError(f"The input {prong1} is bad")
        elif (alpha1[h1] == 0) and (a1 == 0):
            if not ((col1[h1 // 2] == RED) and (col1[hh1 // 2] == BLUE)):
                raise ValueError(f"The corner of {prong1} is not a red-blue corner")
        elif (alpha1[h1] > 0):
            num_v = vt1.half_edge_num_separatrices(h1)
            if a1 not in range(num_v):
                raise ValueError(f"The angle label of {prong1} is out of the valid range [0, {num_v - 1}].")

        #check prong2
        if alpha2[h2] == 0:
            raise ValueError(f"The input {prong2} is not in boundary")
        else:
            num_p = vt2.half_edge_num_separatrices(h2)
            if a2 not in range(num_p):
                raise ValueError(f"The angle label of {prong2} is out of the valid range [0, {num_p}].")

    def _check_prong_matching(self):
        pms = self._prong_matchings()
        l1 = []
        l2 = []
        for pm in pms:
            p1, p2 = pm
            level1, c1, h1, _ = p1
            level2, c2, h2, _ = p2
            vt1 = self._veering_triangulations[level1][c1]
            vt2 = self._veering_triangulations[level2][c2]
            h1 = min(perm_orbit(vt1._vp, h1))
            h2 = min(perm_orbit(vt2._fp, h2))
            if (level1, c1, h1) in l1:
                raise ValueError(f"There are prongs at the same zero as {pm[0]}")
            if (level2, c2, h2) in l2:
                raise ValueError(f"There are prongs at the same pole as {pm[1]}")
            l1.append((level1, c1, h1))
            l2.append((level2, c2, h2))

    def _check_global_residue_conditions(self):
        r"""
        Check the global residue condition.

        EXAMPLES::

            sage: from veerer import *

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[VeeringTriangulationLinearFamily("(0:1)(~0:1)(1:1)(~1:1)(2:1)(~2:1)(3:1)(~3:1)", "RRRR", [(1, 1, 1, 1)])],[VeeringTriangulationLinearFamily("(0:3)(~0:3)(1:3)(~1:3)", "RR", [(1, 1)])]],horizontal_nodes=[[[(0, 2), (1, 4), (3, 5), (6, 7)]], [[]]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 1)), ((0, 0, 4, 0), (1, 0, 3, 1))])
        """
        # Note that there are cases where some levels are Abelian and the other levels are quadratic. The method does not apply to this case yet.
        N = self.num_levels()
        g = self._nodal_digraph
        level_g = g.level_graph(self)
        vertex_labels = g._vertices
        edge_labels = level_g._edges

        abelian, global_oris = self.is_abelian(certificate=True)
        if not abelian:
            return NotImplementedError

        for level in range(1, N):
            components = g.subgraph_above_level(self, level).connected_components(sort=False)
            list_groups = g.vertical_edges_for_GRC(self, level)
            for i, comp in enumerate(components):
                skip = False
                for v in comp:
                    lvl, c, _ = level_g._vertices[v]
                    if not self.without_prescribed_poles(lvl, c):
                        skip = True
                        break
                if skip:
                    continue

                groups = list_groups[i]
                for v in list(groups.keys()):
                    lvl, c = vertex_labels[v]
                    group = groups[v]
                    assert lvl == level
                    vt = self._veering_triangulations[lvl][c]
                    _, oris_vt = vt.is_abelian(certificate=True)

                    base_ring = vt.base_ring()
                    orig_constraints_matrix = vt.constraints_matrix()
                    orig_gens = orig_constraints_matrix.right_kernel_matrix()
                    n1 = orig_constraints_matrix.nrows()
                    constraints_matrix = matrix(base_ring, n1 + 1, vt.num_edges())
                    constraints_matrix[:n1, :] = orig_constraints_matrix

                    bdry = vt.boundary_faces()
                    nf = len(bdry)
                    r1 = vt.residue_matrix()

                    global_oris_vt = global_oris[level][c]
                    ne = vt._ne
                    modify_oris = matrix.identity(ne)
                    for edge in range(ne):
                        if oris_vt[2 * edge] != global_oris_vt[2 * edge]:
                            modify_oris[edge, edge] = - 1

                    rr1 = matrix(ZZ, 1, nf)
                    for e in group:
                        _, _, h, _ = edge_labels[e] # Note that the indices of edges in g and level_g are different
                        for j, f in enumerate(bdry):
                            if h in f:
                                rr1[0, j] = 1
                                break

                    constraints_matrix[n1:, :] = rr1 * r1 * modify_oris
                    gens = constraints_matrix.right_kernel_matrix()

                    if orig_gens != gens:
                        raise ValueError(f"The global residue conditions are not satisfied for the level-{level}")

    def __str__(self):
        vt_strings = ",\n    ".join("[" + ", ".join(str(vt) for vt in l) + "]" for l in self._veering_triangulations)
        horizontal_nodes_str = "[" + ", ".join(str(hn) for hn in self._horizontal_nodes(sort=True)) + "]"
        prong_matching_str = "[" + ", ".join(str(pm) for pm in self._prong_matchings(sort=True)) + "]"
        return (
            f"MultiscaleVeeringTriangulation(\n"
            f"  veering_triangulations=[\n    {vt_strings}\n  ],\n"
            f"  horizontal_nodes={horizontal_nodes_str},\n"
            f"  prong_matchings={prong_matching_str}\n"
            f")"
        )

    def __repr__(self):
        return str(self)

    def __lt__(self, mvt):
        r"""
        EXAMPLES::

            sage: from veerer import *

            sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)])
            sage: vt1 = VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
            sage: mvt0 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0],[vt1]],prong_matchings=[((0, 0, 1, 0), (1, 0, 0, 1)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt1 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt0 < mvt1
            False
            sage: mvt1 < mvt0
            False
        """
        if not isinstance(mvt, type(self)):
            return NotImplemented

        if self._veering_triangulations != mvt._veering_triangulations:
            return NotImplemented

        h_nodes0 = self._horizontal_nodes()
        h_nodes1 = mvt._horizontal_nodes()
        if h_nodes0 != h_nodes1:
            return h_nodes0 < h_nodes1

        pms0 = self._prong_matchings()
        pms1 = mvt._prong_matchings()
        if pms0 != pms1:
            return pms0 < pms1

        return False

    def __eq__(self, other):
        r"""
        Return whether ``self`` and ``other`` are equal.

        EXAMPLES::

            sage: from veerer import *
            sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)])
            sage: vt1 = VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
            sage: mvt0 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0],[vt1]],prong_matchings=[((0, 0, 1, 0), (1, 0, 0, 1)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt1 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt2 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 1)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt0 == mvt1
            True
            sage: mvt0 == mvt2
            False
        """
        if type(self) != type(other):
            raise TypeError
        return (self._veering_triangulations == other._veering_triangulations) and (self._horizontal_nodes() == other._horizontal_nodes()) and (self._prong_matchings() == other._prong_matchings())

    def __ne__(self, other):
        r"""
        Return whether ``self`` and ``other`` are different.

        EXAMPLES::

            sage: from veerer import *
            sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)])
            sage: vt1 = VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
            sage: mvt0 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0],[vt1]],prong_matchings=[((0, 0, 1, 0), (1, 0, 0, 1)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt1 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt2 = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 1)), ((0, 0, 10, 0), (1, 0, 4, 0))])
            sage: mvt0 == mvt1
            True
            sage: mvt0 == mvt2
            False
        """
        if type(self) != type(other):
            raise TypeError
        return (self._veering_triangulations != other._veering_triangulations) and (self._horizontal_nodes() != other._horizontal_nodes()) and (self._prong_matchings() != other._prong_matchings())

    def _cmp_(self, other):
        if type(self) is not type(other):
            raise TypeError

        # number of levels
        c = len(self._veering_triangulations) - len(other._veering_triangulations)
        if c:
            return c

        for self_level, other_level in zip(self._veering_triangulations, other._veering_triangulations):
            # number of prime components in each level
            c = len(self_level) - len(other_level)
            if c:
                return c

            # prime components
            for (self_vt, other_vt) in zip(self_level, other_level):
                c = self_vt._cmp_(other_vt)
                if c:
                    return c

        # horizontal nodes
        self_horiz = self._horizontal_nodes(sort=True)
        other_horiz = other._horizontal_nodes(sort=True)
        c = (self_horiz > other_horiz) - (self_horiz < other_horiz)
        if c:
            return c

        # vertical nodes
        self_vert = self._prong_matchings(sort=True)
        other_vert = other._prong_matchings(sort=True)
        c = (self_vert > other_vert) - (self_vert < other_vert)
        if c:
            return c

        return 0

    def _richcmp_(self, other, op):
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

    def copy(self, mutable=None):
        if mutable is None:
            mutable = self._mutable

        if not mutable and not self._mutable:
            return self

        ans = MultiscaleVeeringTriangulation.__new__(MultiscaleVeeringTriangulation)
        ans._veering_triangulations = [[vt.copy(mutable) for vt in vts] for vts in self._veering_triangulations]
        # TODO: the labelled digraph is always mutable...
        ans._nodal_digraph = self._nodal_digraph.copy()
        ans._mutable = mutable

        return ans

    def set_immutable(self):
        if self._mutable:
            for vts in self._veering_triangulations:
                for vt in vts:
                    vt.set_immutable()
            self._mutable = False

    def __hash__(self):
        """
        TESTS::

            sage: from veerer import *

            sage: f0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)])
            sage: f1 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
            sage: f2 = VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[f0, f1], [f2]], prong_matchings=[[(0, 0, 0, 0), (1, 0, 0, 0)], [(0, 1, 0, 0), (1, 0, 4, 0)]], mutable=False)
            sage: hash(mvt) # random
            313904658927315188
            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[f0, f1], [f2]], prong_matchings=[[(0, 0, 0, 0), (1, 0, 0, 0)], [(0, 1, 0, 0), (1, 0, 4, 0)]], mutable=True)
            sage: hash(mvt)
            Traceback (most recent call last):
            ...
            ValueError: mutable veering triangulation are not hashable
        """
        if self._mutable:
            raise ValueError("mutable veering triangulation are not hashable")
        veering_triangulations_hashable = tuple(tuple(vts) for vts in self._veering_triangulations)
        horizontal_nodes_hashable = tuple(tuple(tuple(comp) for comp in level) for level in self._horizontal_nodes())
        prong_matching_hashable = hash(tuple(self._prong_matchings()))
        return hash((veering_triangulations_hashable, horizontal_nodes_hashable, prong_matching_hashable))

    def num_levels(self):
        return len(self._veering_triangulations)

    # TODO: make it work in the case the veering triangulation are not roots of their Delaunay-Strebel
    # graph. In that situation one needs to transport the nodes at the roots (involving half-edge
    # relabellings and walking through the Delaunay-Strebel graph)
    def linear_subvariety(self):
        r"""
        Return the linear subvariety generated by this multiscale veering triangulation.

        EXAMPLES::

            sage: from veerer import *

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[VeeringTriangulationLinearFamily("(0,5,~4)(~0,~3,4)(1,~2,~5)(~1,2,3)", "RRBBBB", [(1, 0, 0, 0, -1, 0), (0, 1, 0, -1, -1, -1), (0, 0, 1, 1, 1, 1)])],[VeeringTriangulationLinearFamily("(0:2,1:1,~1:2,~0:1)", "RR", [(1, 0), (0, 1)])]],horizontal_nodes=[[[]], [[]]],prong_matchings=[((0, 0, 1, 0), (1, 0, 3, 0))])
            sage: mvt.linear_subvariety()  # optional - surface_dynamics
            Irreducible real linear subvariety of projective dimension 3 in [[H_1(0^2)], [H_0(0^3, -2)]]
        """
        from .linear_subvariety import PrimeDegenerations, IrreducibleRealLinearSubvariety

        P = PrimeDegenerations()
        ds_graphs = []
        mvt = self
        for lvl, vts in enumerate(self._veering_triangulations):
            level = []
            for component, vt in enumerate(vts):
                if vt not in P._to_components:
                    ds_graph = vt.delaunay_strebel_graph()
                    if vt != ds_graph.root():
                        mvt = mvt.transport_to_root(lvl, component, ds_graph)
                    i = P.add(ds_graph)
                else:
                    i = P._to_components[vt]
                level.append(i)
            ds_graphs.append(level)

        return IrreducibleRealLinearSubvariety([[P._components[i] for i in level] for level in ds_graphs], mvt)

    def permute_level(self, level, p):
        r"""
        Apply the permutation ``p`` on the prime components of level ``level``.

        EXAMPLES::

            sage: from veerer import *

            sage: f0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)])
            sage: f1 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
            sage: f2 = VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[f0, f1], [f2]], prong_matchings=[[(0, 0, 0, 0), (1, 0, 0, 0)], [(0, 1, 0, 0), (1, 0, 4, 0)]], mutable=True)
            sage: mvt.permute_level(0, [1, 0])
            sage: mvt
            MultiscaleVeeringTriangulation(
              veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)])],
                [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
              ],
              horizontal_nodes=[[[], []], [[]]],
              prong_matchings=[((0, 0, 0, 0), (1, 0, 4, 0)), ((0, 1, 0, 0), (1, 0, 0, 0))]
            )
        """
        if not self._mutable:
            raise ValueError("immutable multiscale veering triangulation; use a multable copy instead")
        level = self._check_level(level)
        n = len(self._veering_triangulations[level])
        p = perm_init(p, n)
        perm_on_list(self._veering_triangulations[level], p, n)

        # TODO: this is not super clean
        self._nodal_digraph.vertex_relabelling({(l, c): (l, p[c]) for (l, c) in self._nodal_digraph._vertices if l == level})

        self._check()

    def horizontal_faces(self, level, c, node):
        r"""
        Return a pair of faces corresponding to the node
        """
        level = self._check_level(level)
        h1, h2 = node

        vt = self._veering_triangulations[level][c]

        return (perm_orbit(vt._fp, h1), perm_orbit(vt._fp, h2))

    def without_prescribed_poles(self, level, comp):
        r"""
        Return True if every boundary face in the component is adjacent to either a horizontal or vertical node.
        Otherwise, return False.

        EXAMPLES::
            sage: from veerer import *

            sage: vt = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)", "RBRBB")
            sage: mvt = MultiscaleVeeringTriangulation([vt])
            sage: mvt1 = list(mvt.codimension_one_vertical_degenerations())[1]
            sage: mvt1.without_prescribed_poles(0,0)
            False
            sage: mvt1.without_prescribed_poles(1,0)
            True
        """
        level = self._check_level(level)
        g = self._nodal_digraph
        vertex_labels = g._vertices
        edge_labels = g._edges
        vt = self._veering_triangulations[level][comp]

        v = vertex_labels.index((level, comp))
        edges = set(g.adjacent_edges(v))

        for f in vt.boundary_faces():
            skip = False
            for e in edges:
                label_e = edge_labels[e]
                if len(label_e) == 2:
                    h1, h2 = label_e
                    if (h1 in f) or (h2 in f):
                        skip = True
                        break
                else:
                    h1, _, h2, _ = label_e
                    if (g.vertex_level(g.edge_target(e)) == level) and (h2 in f):
                        skip = True
                        break
            if skip:
                continue
            return False
        return True

    def is_abelian(self, certificate=False):
        r"""
        Return whether the multi-scale veering triangulation is Abelian.

        EXAMPLES::

            sage: from veerer import *

        A horizontal node between the same components::

            sage: vt = VeeringTriangulationLinearFamily("(0,1,4)(2,3,~4)(~0:1)(~1:1)(~2:1)(~3:1)", "RBBRR", [(1, 0, 0, 1, 1), (0, 1, 1, -2, -1)])
            sage: mvt = MultiscaleVeeringTriangulation([vt],[["(~1,~2)"]],[])
            sage: mvt.is_abelian()
            False

        Mix of horizontal and vertical nodes::

            sage: vt0 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)", "RBRBB")
            sage: vt1 = VeeringTriangulationLinearFamily("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(2:1)(~3:1)(~4:1)(5:5)(7:1)(~8:1)(~9:1)", "BBRBRBBRBR", [(1, 0, 0, 0, 1, 0, 0, 1, 1, 0), (0, 1, 0, 1, -1, 0, 0, -1, -1, 0), (0, 0, 1, 1, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 1, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, 1, 0, 1, -1)])
            sage: vt0.is_abelian()
            True
            sage: vt1.is_abelian()
            True
            sage: mvt0 = MultiscaleVeeringTriangulation([vt0,vt1],[[[]],[[(9,14)]]],[[(0,0,0,0),(-1,0,0,1)],[(0,0,4,0),(-1,0,10,1)]])
            sage: mvt0.is_abelian()
            False
            sage: vt2 = VeeringTriangulationLinearFamily("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(2:1)(~3:1)(~4:1)(5:5)(7:1)(~8:1)(~9:1)", "BBRBRBBRBR", [(1, 0, 0, 0, 1, 0, 0, 0, 0, 0), (0, 1, 0, 1, -1, 0, 0, 1, 1, 0), (0, 0, 1, 1, 0, 0, 0, 1, 1, 0), (0, 0, 0, 0, 0, 1, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, 1, -1, 0, -1)])
            sage: mvt1 = MultiscaleVeeringTriangulation([vt0,vt2],[[[]],[[(7,17)]]], [[(0,0,0,0),(-1,0,0,1)],[(0,0,4,0),(-1,0,10,1)]])
            sage: print(mvt1.is_abelian(certificate=True))
            (True, [[[True, False, True, False, False, True, False, True, False, True]], [[False, True, False, True, False, True, False, True, False, True, True, False, True, False, True, False, True, False, True, False]]])
        """
        # compute orientations of each vertex
        oris = []
        for vts in self._veering_triangulations:
            cur_oris = []
            for vt in vts:
                abelian, orient = vt.is_abelian(certificate=True)
                if not abelian:
                    return (False, None) if certificate else False
                cur_oris.append(orient)
            oris.append(cur_oris)

        g = self._nodal_digraph.level_graph(self)
        vertex_labels = g._vertices
        edge_labels = g._edges
        vertices = set(range(len(vertex_labels)))

        while vertices:
            #propagete the orientation in the connected component containing the vertex v.
            v0 = vertices.pop()
            l0 = g.adjacent_edges(v0)
            lv = {v0} #the vertices visited so far
            le = set() #the edges visited so far
            while l0:
                e = l0.pop()
                le.add(e)
                label_e = edge_labels[e]
                v1, v2 = g.edge_source(e), g.edge_target(e)
                level1, s1, c1 = vertex_labels[v1]
                level2, s2, c2 = vertex_labels[v2]
                vt1 = self._veering_triangulations[level1][s1]
                vt2 = self._veering_triangulations[level2][s2]

                #horizontal node
                if len(label_e) == 2:
                    assert level1 == level2 and s1 == s2 and vt1 == vt2
                    h1, h2 = label_e
                    assert h1 < h2
                    lo = oris[level1][s1]
                    o1, o2 = lo[h1], lo[h2]

                    # check coherence
                    if o1 == o2:
                        if v1 == v2 or ((v1 in lv) and (v2 in lv)):
                            return (False, None) if certificate else False
                        if v1 not in lv: # rotate the component v1 by pi
                            for h in range(len(lo)):
                                if h // 2 in vt1.connected_components()[c1]:
                                    lo[h] = not lo[h]
                        elif v2 not in lv: # rotate the component v2 by pi
                            for h in range(len(lo)):
                                if h // 2 in vt1.connected_components()[c2]:
                                    lo[h] = not lo[h]
                    oris[level1][s1] = lo

                #vertical node
                else:
                    h1, ang1, h2, ang2 = edge_labels[e]
                    lo1 = oris[level1][s1]
                    lo2 = oris[level2][s2]
                    # Adjust the prong orientation based on the angle
                    o1 = not lo1[h1] if (ang1 % 2 == 1) else lo1[h1]
                    o2 = not lo2[h2] if (ang2 % 2 == 1) else lo2[h2]

                    if o1 != o2:
                        if (v1 in lv) and (v2 in lv):
                            return (False, None) if certificate else False
                        if v1 not in lv: # rotate the component v1 by pi
                            for h in range(len(lo1)):
                                if h // 2 in vt1.connected_components()[c1]:
                                    lo1[h] = not lo1[h]
                        elif v2 not in lv: # rotate the component v2 by pi
                            for h in range(len(lo2)):
                                if h // 2 in vt2.connected_components()[c2]:
                                    lo2[h] = not lo2[h]
                    oris[level1][s1] = lo1
                    oris[level2][s2] = lo2

                lv.update([v1, v2])
                v_next = v2 if v1 == v0 else v1 # determine the next vertex
                if v_next in vertices:
                    vertices.remove(v_next)
                v0 = v_next
                l0 = [e for e in g.adjacent_edges(v0) if e not in le]

        return (True, oris) if certificate else True

    # TODO: this should be used to check that degeneration does produce mvt in the same
    # ambient stratum
    # TODO: maybe we want to changed the name as the ambient stratum could be the generalized
    # stratum (in the sense of admcycles)
    def ambient_stratum(self, multiscale_structure=False):
        r"""
        Return the ambient stratum of the multi-scale veering triangulation.

        If ``multiscale_structure`` is True, return the stratum for each vertex of the level graph. Otherwise, return the stratum of the veering triangulation by collapsing all the nodes of the multi-scale veering triangulation.

        EXAMPLES::

            sage: from veerer import *

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,~5)", "RRBBRR", [(1, 0, -1, -1, 0, -1), (0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1)])],[VeeringTriangulationLinearFamily("(0:1)(~0:3)(1:1)(~1:3)", "RR", [(1, 1)])]], horizontal_nodes=[[[]], [[(0, 2)]]], prong_matchings=[((0, 0, 0, 0), (1, 0, 1, 0)), ((0, 0, 1, 0), (1, 0, 3, 0))])

        When ``multiscale_structure`` is False::

            sage: mvt.ambient_stratum()  # optional - surface dynamics
            H_2(1^2)

        When ``multiscale_structure`` is True::

            sage: mvt.ambient_stratum(multiscale_structure=True)  # optional - surface dynamics
            [[H_1(0^2)], [(H_0(1, -1, -2), H_0(1, -1, -2))]]
        """
        g = self._nodal_digraph

        if not g._digraph.is_connected():
            return NotImplemented

        if not multiscale_structure:
            # build the collection of all angles
            from collections import defaultdict
            angles = defaultdict(int)
            for vts in self._veering_triangulations:
                for vt in vts:
                    for a in vt.angles():
                        angles[a] += 1

            is_abelian = all(a % 2 == 0 for a in angles) and self.is_abelian()

            # remove angles attached to nodes
            for e in range(g.num_edges()):
                u = g.edge_source(e)
                v = g.edge_target(e)
                if u == v:
                    # horizontal node
                    assert angles[0] >= 2
                    angles[0] -= 2
                else:
                    # vertical node
                    assert g.vertex_level(v) > g.vertex_level(u)
                    (l0, c0) = g.vertex_label(u)
                    (l1, c1) = g.vertex_label(v)
                    (h0, a0, h1, a1) = g.edge_label(e)

                    a = self._veering_triangulations[l0][c0].vertex_angle(h0)
                    assert angles[a] >= 1
                    angles[a] -= 1

                    a = self._veering_triangulations[l1][c1].face_angle(h1)
                    assert angles[a] >= 1
                    angles[a] -= 1

            angles = [a for a, num in angles.items() for _ in range(num)]

            from .features import surface_dynamics_feature
            surface_dynamics_feature.require()

            from surface_dynamics.flat_surfaces.strata import Stratum

            if is_abelian:
                return Stratum([(a - 2) // 2 for a in angles], 1)
            else:
                return Stratum([(a - 2) for a in angles], 2)

        l = []
        N = self.num_levels()
        for level in range(N):
            l.append([])
            for vt in self._veering_triangulations[level]:
                from .features import surface_dynamics_feature
                surface_dynamics_feature.require()

                from surface_dynamics.flat_surfaces.strata import Stratum
                l[level].append(vt.stratum())
        return l

    def degeneration(self, level, component, edges_low=None, edges_up=None):
        r"""
        Return the multi-scale veering triangulation by blowing-up the given subset of edges.

        This corresponds to an either a horizontal degeneration or a vertical degeneration in the BCGGM compactification.

        EXAMPLES::

            sage: from veerer import *

        Reach all vertical boundary component of H_1(2) from a single veering triangulaiton (TO BE COMPLETED)::

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BRBBRBBRB")
            sage: vt.stratum()  # optional - surface_dynamics
            H_2(2)
            sage: mvt = MultiscaleVeeringTriangulation([vt],[[""]],[])
            sage: vt.vertical_degeneration_low_edges_subsets()
            [(1,), (4,), (7,), (4, 7), (1, 4)]
            sage: mvt1 = mvt.degeneration(0,0, edges_low=(1,))
            sage: mvt2 = mvt.degeneration(0,0, edges_low=(4,))
            sage: mvt3 = mvt1.degeneration(0,0, edges_low=(4,))

        More examples::

            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01], prong_matchings=[[(0,0,0,0),(-1,0,0,1)],[(0,0,4,0),(-1,0,10,1)]])
            sage: mvt0.degeneration(-1,0, edges_low=[0, 1, 2, 3, 4, 5], edges_up=[6, 7])
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)", "RBRBB")],
                [VeeringTriangulationLinearFamily("(~0,1,2)(~1,~2,3)(0:5)(~3:1)(4:4,5:4)(~4:1)(~5:1)", "BBRBBB", [(1, 0, 1, 1, 0, 0), (0, 1, -1, 0, 0, 0), (0, 0, 0, 0, 1, 1)])]
            ],
            horizontal_nodes=[[[]], [[(9, 11)]]],
            prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 1)), ((0, 0, 4, 0), (1, 0, 10, 1))]
            )
        """
        level = self._check_level(level)

        vts = copy.deepcopy(self._veering_triangulations)
        vt = vts[level][component]
        nh = 2 * (vt.num_edges())
        ep = vt.edge_permutation()

        f_up ,f_low, r_up, r_low = vt.degeneration(edges_low=edges_low, edges_up=edges_up, collapsed_half_edge_relabelling=True)

        #build list of veering triangulations.
        if f_up is None:
            vts[level][component] = f_low
        else:
            vts[level][component] = f_up
            vts.insert(level + 1, [f_low])

        # build the horizontal nodes.
        l1 = [] #new horizontal nodes at (level, component)
        l2 = [] #new horizontal nodes at (level - 1, 0) if the degeneration has two levels
        l_horiz = self._horizontal_nodes()

        # existing horizontal nodes
        for h1, h2 in self._horizontal_nodes()[level][component]:
            prong1 = (level, component, h1, 0)
            prong2 = (level, component, h2, 0)
            newprong1 = track_prong(vt, r_up, r_low, prong1, vertex=False, face=True)
            newprong2 = track_prong(vt, r_up, r_low, prong2, vertex=False, face=True)
            newh1 = newprong1[2]
            newh2 = newprong2[2]
            assert newprong1[0] == newprong2[0]
            
            if newprong1[0] == level:
                l1.append((newh1, newh2))
            else:
                l2.append((newh1, newh2))

        # new horizontal nodes
        if f_up is None: #horizontal degeneration
            for h in range(nh):
                if (r_up[h] == r_low[h] == -1):

                    def bdry_of_cyl(vt, r_low, h):
                        while r_low[h] == -1:
                            h = vt.previous_at_vertex(h)
                        return r_low[h]

                    b1 = bdry_of_cyl(vt, r_low, h)
                    h1 = ep[h]
                    b2 = bdry_of_cyl(vt, r_low, h1)

                    #add the corresponding horizontal node
                    assert f_low.face_angle(b1) == f_low.face_angle(b2) == 0
                    for f in f_low.boundary_faces():
                        if b1 in f:
                            b1 = min(f)
                        if b2 in f:
                            b2 = min(f)
                    node = tuple(sorted((b1, b2)))
                    if node not in l1:
                        l1.append(node)
            l_horiz[level][component] = l1
        else:
            l_horiz.insert(level + 1, [[]])
            l_horiz[level][component] = l1
            l_horiz[level + 1][0] = l2

        #build the vertical nodes
        l_pm = []
        #existing vertical nodes
        original_pm = self._prong_matchings()
        for prong1, prong2 in original_pm:
            if prong1[0] == level and prong1[1] == component:
                prong1 = track_prong(vt, r_up, r_low, prong1, vertex=True)
                if f_up is not None:
                    prong2 = (prong2[0] + 1,prong2[1], prong2[2], prong2[3])
            elif prong2[0] == level and prong2[1] == component:
                prong2 = track_prong(vt, r_up, r_low, prong2, face=True)
            elif prong1[0] < level and prong2[0] > level:
                if f_up is not None:
                    prong2 = (prong2[0] + 1,prong2[1], prong2[2], prong2[3])
            elif prong1[0] > level:
                assert prong2[0] > level
                if f_up is not None:
                    prong1 = (prong1[0] + 1,prong1[1], prong1[2], prong1[3])
                    prong2 = (prong2[0] + 1,prong2[1], prong2[2], prong2[3])
            l_pm.append([prong1,prong2])
        #new vertical nodes
        if f_up is not None:
            l_pm  = l_pm + new_prong_matching(vt, f_low, r_up, r_low, level, component)

        #build the degeneration
        return MultiscaleVeeringTriangulation(vts, l_horiz, l_pm)

    def codimension_one_horizontal_degenerations(self, level=None, component=None):
        r"""
        Iterator through the list of codimension one horizontal degenerations.

        INPUT:

        - ``level`` -- optional integer

        - ``component`` -- optional integer
        """
        if level is None:
            for level in range(self.num_levels()):
                for component in range(len(self._veering_triangulations[level])):
                    yield from self.codimension_one_horizontal_degenerations(level, component)
            return
        if component is None:
            for component in range(len(self._veering_triangulations[level])):
                yield from self.codimension_one_horizontal_degenerations(level, component)
            return

        for edges in self._veering_triangulations[level][component].horizontal_degeneration_up_edges_subsets():
            yield self.degeneration(level, component, edges_up=edges)

    def codimension_one_vertical_degenerations(self, level=None, component=None):
        r"""
        Iterator through the list of codimension one vertical degenerations.

        INPUT:

        - ``level`` -- optional integer

        - ``component`` -- optional integer

        EXAMPLES::

            sage: from veerer import *

            sage: vt = VeeringTriangulationLinearFamily("(~0,2,3)(~1,4,5)(~2,6,7)(~3,~5,8)(~4,9,10)(~6,11,12)(~7,13,14)(~8,~12,15)(~9,16,~15)(~11,17,18)(~14,~18,19)(~16,~17,20)(0:1)(1:1)(~10:1)(~13:1)(~19:1)(~20:1)", "BBRRRBBBRBBRRBRBRRBBB", [(1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, 1, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 1, 1), (0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1, 0, 0, -1, 1, 1, 1, 0, 0, -1, -1), (0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, -1, -1), (0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, -1, 0, -1, 0, 0, 1, 1), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, -1, -1, -1), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1)])
            sage: L = vt.linear_subvariety() # not tested
            sage: l = list(L.codimension_one_vertical_degenerations()) # not tested

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])], [VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)])]], horizontal_nodes=[[[]], [[]]], prong_matchings=[((0, 0, 0, 0), (1, 0, 3, 0))])
            sage: L = mvt.linear_subvariety()
            sage: l0 = list(L.codimension_one_vertical_degenerations(0))
            sage: l1 = list(L.codimension_one_vertical_degenerations(1))
        """
        if level is None:
            for level in range(self.num_levels()):
                for component in range(len(self._veering_triangulations[level])):
                    yield from self.codimension_one_vertical_degenerations(level, component)
            return
        if component is None:
            for component in range(len(self._veering_triangulations[level])):
                yield from self.codimension_one_vertical_degenerations(level, component)
            return

        for edges in self._veering_triangulations[level][component].vertical_degeneration_low_edges_subsets():
            yield self.degeneration(level, component, edges_low=edges)

    def replace_veering_triangulation(self, level, component, veering_triangulation, framing=None, original_framing=None):
        r"""
        Replace the veering triangulation at ``(level, component)`` in this
        multiscale veering triangulation.

        In order to make sense, the veering triangulation used for replacement
        must belong to the same stratum.

        INPUT:

        - ``level``, ``component`` -- the indices of the prime component to replace

        - ``veering_triangulation`` -- the veering triangulation used to replace the current one

        - ``framing`` -- an optional framing for ``veering_triangulation``

        - ``original_framing`` -- an optional framing for the current veering triangulation

        EXAMPLES::

            sage: from veerer import *
            sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,~5)", "RRBBRR", [(1, 0, -1, -1, 0, -1), (0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1)])
            sage: vt1 = VeeringTriangulationLinearFamily("(0:1)(~0:3)(1:1)(~1:3)", "RR", [(1, 1)])
            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]], horizontal_nodes=[[[]], [[(0, 2)]]], prong_matchings=[((0, 0, 0, 0), (1, 0, 1, 0)), ((0, 0, 1, 0), (1, 0, 3, 0))], mutable=True)
            sage: mvt.ambient_stratum()  # optional - surface dynamics
            H_2(1^2)
            sage: mvt.replace_veering_triangulation(0, 0, VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,~5)", "RRBBRB", [(1, 0, -1, -1, 0, -1), (0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1)]))
            sage: mvt.ambient_stratum()  # optional - surface dynamics
            H_2(1^2)

            sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
            sage: vt1 = VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)])
            sage: mvt = MultiscaleVeeringTriangulation([vt0, vt1], horizontal_nodes=[[[]], [[]]], prong_matchings=[((0, 0, 0, 0), (1, 0, 2, 0))], mutable=True)
            sage: vt = VeeringTriangulationLinearFamily("(0:1,1:2,~0:1,~1:2)", "RR", [(1, 0), (0, 1)])
            sage: mvt.replace_veering_triangulation(1, 0, vt, framing=([(3, 0)], [(3, 0)], [], []), original_framing=([(0, 0)], [(0, 0)], [], []))
            sage: mvt._check()
        """
        if not self._mutable:
            raise ValueError
        if original_framing is None:
            original_framing = self._veering_triangulations[level][component].framing()
        if framing is None:
            framing = veering_triangulation.framing()

        # NOTE: original_indices is a 6-tuple
        original_indices = self._veering_triangulations[level][component].framing_indices(original_framing)
        vseps_indices, vseps_angles, fseps_indices, fseps_angles, cseps_indices, fhedges_indices = original_indices
        new_separatrices = veering_triangulation.framing_separatrices(framing)

        # relabel edges in the nodal graph
        # TODO: we would better not access internals of LabelledDiGraph here
        D = self._nodal_digraph
        i = D.vertex_index((level, component))
        for e in D.outgoing_edges(i, reverse=False):
            target_level, target_component = D._vertices[D._edge_targets[e]]
            if level == target_level:
                # horizontal edge
                assert component == target_component
                (h0, h1) = self._nodal_digraph._edges[e]
                h0_new = new_separatrices[original_indices[4][h0]]
                h1_new = new_separatrices[original_indices[4][h1]]
                D._edges[e] = (h0_new, h1_new)
            else:
                # vertical edge
                assert target_level > level
                (h0, a0, h1, a1) = self._nodal_digraph._edges[e]
                h0_new, a0_new = new_separatrices[vseps_indices[(h0, a0)]][vseps_angles[(h0, a0)]]
                D._edges[e] = (h0_new, a0_new, h1, a1)

        for e in D.incoming_edges(i, reverse=False):
            source_level, source_component = D._vertices[D._edge_sources[e]]
            if level == source_level:
                # horizontal edge (these are loops and have been treated in the previous loop)
                assert component == source_component
                continue
            else:
                # vertical edge
                assert level > source_level
                (h0, a0, h1, a1) = self._nodal_digraph._edges[e]
                h1_new, a1_new = new_separatrices[fseps_indices[(h1, a1)]][fseps_angles[(h1, a1)]]
                D._edges[e] = (h0, a0, h1_new, a1_new)

        self._veering_triangulations[level][component] = veering_triangulation

    def set_canonical_labels(self, level, comp):
        r"""
        Return the multi-scale veering triangulation with the veering triangulation at ``(level, comp)`` set the canonical label.

        EXAMPLES::

            sage: from veerer import *

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBR", [(1, 0, 1), (0, 1, -1)])],[VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]],horizontal_nodes=[[[], []], [[]]],prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 1, 4, 0), (1, 0, 4, 0))])
            sage: mvt = mvt.copy(mutable=True)
            sage: mvt.set_canonical_labels(0, 1)
            sage: mvt
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])],
                [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
            ],
            horizontal_nodes=[[[], []], [[]]],
            prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 1, 0, 0), (1, 0, 4, 0))]
            )
        """
        if not self._mutable:
            raise ValueError

        level = self._check_level(level)

        vt = self._veering_triangulations[level][comp]
        mapping = vt.set_canonical_labels(mapping=True)
        self._veering_triangulations[level][comp] = vt

        #change the labels of the edges of the nodal graph
        D = self._nodal_digraph
        for e, label in enumerate(D._edges):
            l1, c1 = D._vertices[D.edge_source(e)]
            l2, c2 = D._vertices[D.edge_target(e)]
            if len(label) == 2:
                (h1, h2) = label
                if l1 == l2 == level and c1 == c2 == comp:
                    h1 = mapping[h1]
                    h2 = mapping[h2]
                    # normalize the node
                    vt = self._veering_triangulations[l1][c1]
                    fp = vt.face_permutation()
                    h1 = min(perm_orbit(fp, h1))
                    h2 = min(perm_orbit(fp, h2))
                    h1, h2 = sorted([h1, h2])
                    D._edges[e] = (h1, h2)
            elif len(label) == 4:
                h1, ang1, h2, ang2 = label
                if (l1, c1) == (level, comp):
                    h1 = mapping[h1]
                if (l2, c2) == (level, comp):
                    h2 = mapping[h2]
                # normalize the node
                ((l1, c1, h1, ang1), (l2, c2, h2, ang2)) = self._normalize_prong_matching(((l1, c1, h1, ang1), (l2, c2, h2, ang2)))
                D._edges[e] = ((h1, ang1, h2, ang2))

    def transport_to_root(self, level, component, ds_graph):
        r"""
        Return the multi_scale veering triangulation by transport the veering triangulation at ``(level, component)`` along its Delaunay-Strebel graph to the root.

        EXAMPLES::

            sage: from veerer import *

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[VeeringTriangulationLinearFamily("(0,5,~4)(~0,~3,4)(1,~2,~5)(~1,2,3)", "RRBBBB", [(1, 0, 0, 0, -1, 0), (0, 1, 0, -1, -1, -1), (0, 0, 1, 1, 1, 1)])],[VeeringTriangulationLinearFamily("(0:2,1:1,~1:2,~0:1)", "RR", [(1, 0), (0, 1)])]],horizontal_nodes=[[[]], [[]]],prong_matchings=[((0, 0, 1, 0), (1, 0, 3, 0))])
            sage: vt1 = mvt._veering_triangulations[0][0]
            sage: ds_graph1 = vt1.delaunay_strebel_graph()
            sage: vt2 = mvt._veering_triangulations[1][0]
            sage: ds_graph2 = vt2.delaunay_strebel_graph()
            sage: mvt1 = mvt.transport_to_root(0, 0, ds_graph1)
            sage: mvt2 = mvt1.transport_to_root(1, 0, ds_graph2)
            sage: mvt2
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,~5)", "RRBBRR", [(1, 0, -1, -1, 0, -1), (0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1)])],
                [VeeringTriangulationLinearFamily("(0:1,~0:2,1:1,~1:2)", "RR", [(1, 0), (0, 1)])]
            ],
            horizontal_nodes=[[[]], [[]]],
            prong_matchings=[((0, 0, 1, 0), (1, 0, 3, 0))]
            )
        """
        level = self._check_level(level)
        mvt = self.copy(mutable=True)
        mvt.set_canonical_labels(level, component)
        original_vt = mvt._veering_triangulations[level][component]
        original_vt.set_immutable()
        original_framing = ds_graph.framing(ds_graph.vertex_index(original_vt))
        vt = ds_graph.root()
        vt_framing = ds_graph.framing(0)
        mvt.replace_veering_triangulation(level, component, vt, framing=vt_framing, original_framing=original_framing)
        mvt.set_immutable()
        return mvt

    # TODO: prime_decomposition should not call set_canonical_labels
    def prime_decomposition(self, level, component):
        r"""
        Return a prime decomposition of a component at ``(level, component)`` of multi-scale veering triangulation.

        EXAMPLES::

            sage: from veerer import *

            sage: vt = VeeringTriangulation("(0,1,2)(4,~2,3)(~3,5,6)(~6,~0,~1)(11, 12,~10)(8,9,10)(~13, 7, ~9)(13,~11,~12)(~5,~7,14)(~14,~4,~8)", "RBBBRRBBBRRBRRB")
            sage: edges_low = [4,5,7,8,14]
            sage: mvt = MultiscaleVeeringTriangulation([vt], [[""]], [])
            sage: mvt1 = mvt.degeneration(0,0,edges_low=edges_low)
            sage: mvt1
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)])],
                [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
            ],
            horizontal_nodes=[[[]], [[]]],
            prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 10, 0), (1, 0, 4, 0))]
            )
            sage: mvt1.prime_decomposition(0, 0)
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBR", [(1, 0, 1), (0, 1, -1)])],
                [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
            ],
            horizontal_nodes=[[[], []], [[]]],
            prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 1, 4, 0), (1, 0, 4, 0))]
            )
        """
        level = self._check_level(level)
        vts = copy.deepcopy(self._veering_triangulations)
        vt = vts[level][component]
        l = vt.prime_decomposition()

        #store the prime component and mapping to the canonical labels
        l_comp = []
        l_vts = []
        for edges, vt_prime in l:
            l_comp.append(edges)
            l_vts.append(vt_prime)

        #build veering triangulations
        vts[level][component : component + 1] = l_vts

        def label_in_prime_comp(h, l_comp):
            for c, edges in enumerate(l_comp):
                if h // 2 in edges:
                    i = edges.index(h // 2)
                    if h%2 == 0:
                        return (c, 2 * i)
                    else:
                        return (c, 2 * i + 1)

        #new horizontal nodes
        l1 = [[] for i in range(len(l))]
        l_horiz = self._horizontal_nodes()
        for h1, h2 in l_horiz[level][component]:
            cp1, h1 = label_in_prime_comp(h1, l_comp)
            cp2, h2 = label_in_prime_comp(h2, l_comp)
            assert cp1 == cp2
            l1[cp1].append((h1,h2))
        l_horiz[level][component:component + 1] = l1

        #new vertical nodes
        l2 = []
        l_vert = self._prong_matchings()
        for pm in l_vert:
            p1, p2 = pm
            level1, c1, h1, ang1 = p1
            level2, c2, h2, ang2 = p2
            if (level1, c1) == (level, component):
                cp1, h1 = label_in_prime_comp(h1, l_comp)
                p1 = (level, cp1 + component, h1, ang1)
            if (level2, c2) == (level, component):
                cp2, h2 = label_in_prime_comp(h2, l_comp)
                p2 = (level, cp2 + component, h2, ang2)
            if level1 == level and c1 > component:
                p1 = (level, c1 + len(l_vts) - 1, h1, ang1)
            if level2 == level and c2 > component:
                p2 = (level, c2 + len(l_vts) - 1, h2, ang2)
            l2.append([p1,p2])
        l_vert = l2

        mvt = MultiscaleVeeringTriangulation(vts,l_horiz,l_vert)
        return mvt
