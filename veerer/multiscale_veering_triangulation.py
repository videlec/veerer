r"""
Multi-scale Veering Triangulations
"""

from array import array
import itertools
import numbers

from sage.structure.element import Matrix
from sage.rings.integer_ring import ZZ
from sage.matrix.constructor import matrix
from sage.matrix.special import identity_matrix

from .permutation import perm_check, perm_cycles, perm_cycles_to_string, str_to_cycles, str_to_cycles_and_data, perm_init
from .triangulation import Triangulation
from .veering_triangulation import *
from .constants import *
from .polyhedron import *
from .labelled_digraph import *
from .monodromy import *


# TODO: Store the data of horizontal and vertical nodes in terms of LabeleddDiGraph

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

def track_prong(vt, r_up, r_low, prong):
    l, c, h, ang = prong
    l = abs(l)

    for v in vt.vertices():
        if h in v:
            v1 = v
    vh = [r_up[h] for h in v1]

    if min(vh) >= 0: #The case that vh is in f_up
        h = r_up[h]
        return (l, c, h, ang)
    else: #The case that vh is in f_low
         if max(r_up) == -1:
            return (l, c, r_low[h],ang)
         else:
            a = 0
            while r_up[h] >= 0:
                c1 = vt._colouring[h // 2]
                h = vt.previous_at_vertex(h)
                c2 = vt._colouring[h // 2]
                if (c2 == RED) and (c1 == BLUE):
                    a = a + 1
            ang = ang + a
            assert r_low[h] >= 0
            return (l + 1, 0, r_low[h], ang)

def _vaninshing_red_blue_corner(vt, r_up, r_low, h):
    hh = vt.next_at_vertex(h)
    if r_up[h] >= 0 and r_low[hh] >= 0 and vt.boundary_vector()[h] == 0 and vt.half_edge_num_separatrices(h) == 1:
        return True
    else:
        return False

def _new_prong_matching(vt, f_low, r_up, r_low, level, comp):
    level = abs(level)
    nh = 2 * vt.num_edges()
    newpm = []
    lpoles = [] #the poles at nodes in f_low considered so far
    for h in range(nh):
        hh = vt.next_at_vertex(h)
        if r_up[h] >= 0 and r_low[hh] >= 0:
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
                    prong2 = track_prong(vt, r_up, r_low, vert_sep)
                    assert prong2[0] == level + 1
                    pm = [prong1, prong2]
                    newpm.append(pm)
                    lpoles.append(f_pole)
    return newpm

def tree_with_target(self, root=0, target_vertices=[]):
    """
    Return paths to all target vertices, preserving the order of target_vertices.
    """
    tree = [None] * len(self)
    seen = [False] * len(self)
    seen[root] = True
    todo = [root]

    path_dic = {}
    paths = [None] * len(target_vertices)
    while todo:
        v = todo.pop()
        if v in target_vertices and v not in path_dic:
            path = []
            current = v
            while current != root:
                edge = tree[current]
                path.append(edge)
                current = self.edge_target(edge)
            path = [-(e + 1) for e in path]
            path.reverse()
            path_dic[v] = LabelledDiGraphPath(self, 0, path)

        for i in self.incoming_edges(v):
            u = self.edge_source(i)
            if not seen[u]:
                tree[u] = i
                seen[u] = True
                todo.append(u)

        for i, target in enumerate(target_vertices):
            paths[i] = path_dic.get(target)
    return paths

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
        sage: vt.stratum()
        H_3(4)
        sage: vt.is_delaunay()
        True
        sage: edges_low = [4,5,7,8,14]
        sage: mvt = MultiscaleVeeringTriangulation([vt], [[""]], [])
        sage: mvt1 = mvt.degeneration(0, 0, edges_low=edges_low)
        sage: mvt1
        MultiscaleVeeringTriangulation(
        veering_triangulations=[
            [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)])],
            [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
        ],
        horizontal_nodes=[[[]], [[]]],
        prong_matching=[[(0, 0, 0, 0), (1, 0, 0, 0)], [(0, 0, 10, 0), (1, 0, 4, 0)]]
        )
        sage: vt0 = mvt1._veering_triangulations[0][0]
        sage: vt1 = mvt1._veering_triangulations[1][0]
        sage: vt0.stratum()
        (H_1(0), H_1(0))
        sage: vt1.stratum()
        H_1(4, -2^2)
        sage: vt1.residue_constraints()
        [1 0]
        [0 1]
    """

    def __init__(self, veering_triangulations=None, horizontal_nodes=None, prong_matching=None, mutable=False, check=True):
        if isinstance(veering_triangulations, list):
            self._veering_triangulations = []
            for level, vts in enumerate(veering_triangulations):
                if isinstance(vts, VeeringTriangulation):
                    self._veering_triangulations.append([vts])
                elif isinstance(vts, list):
                    for vt in vts:
                        if not isinstance(vt, VeeringTriangulation):
                            raise TypeError(f"'vt' (value: {vt}) is not an instance of the VeeringTriangulation.")
                    self._veering_triangulations.append(list(vts))
                else:
                    raise ValueError(f"The input of veering triangulations {vts} at level-{level} is bad.")
        else:
            raise ValueError("The 'veering_triangulations' must be a list.")

        if isinstance(horizontal_nodes, list):
            if len(horizontal_nodes) != len(self._veering_triangulations):
                raise ValueError("Miss information for horizontal nodes at some levels")
            self._horizontal_nodes = []
            data_horiz_nodes =[] #the data used to build the digraph
            for level in range(len(horizontal_nodes)):
                self._horizontal_nodes.append([])
                nodes = horizontal_nodes[level]
                vts = self._veering_triangulations[level]
                if len(nodes) != len(vts):
                    raise ValueError(f"Miss information for horizontal nodes at some components at level-{level}")
                for c in range(len(vts)):
                    self._horizontal_nodes[level].append([])
                    nodes_at_c = []
                    vt = vts[c]
                    if isinstance(nodes[c], list):
                        if all(len(n) == 2 for n in nodes[c]):
                            nodes_at_c = nodes[c]
                        else:
                            raise ValueError(f"The input of horizontal nodes {nodes[c]} is bad.")
                    elif isinstance(nodes[c], str):
                        n = str_to_cycles(nodes[c])
                        for i in range(len(n)):
                            node = n[i]
                            for j in range(2):
                                h = node[j]
                                if h < 0:
                                    h = -2 * h - 1
                                else:
                                    h = 2 * h
                                node[j] = vt._check_half_edge(h)
                                n[i] = node
                        nodes_at_c = n
                    else:
                        raise ValueError(f"The input of horizontal nodes of the {c}-th component at level-{level} is bad")

                    # normalization of horizontal nodes
                    fp = vt.face_permutation()
                    for node in nodes_at_c:
                        h1, h2 = node
                        h1 = min(perm_orbit(fp, h1))
                        cc1 = in_connected_component(vt,h1)
                        h2 = min(perm_orbit(fp, h2))
                        cc2= in_connected_component(vt, h2)
                        node = tuple(sorted((h1, h2)))
                        if check:
                            self._check_horizontal_node(level, c, node)
                        self._horizontal_nodes[level][c].append(node)
                        data_horiz_nodes.append((level, c, cc1, h1, cc2, h2))
                    self._horizontal_nodes[level][c] = sorted(self._horizontal_nodes[level][c], key=lambda x: x[0])
        elif horizontal_nodes is None:
            self._horizontal_nodes = [[[] for _ in range(len(vts))] for vts in self._veering_triangulations]
        else:
            raise TypeError("The 'horizontal_nodes' must be a list; got {}".format(type(horizontal_nodes)))

        if isinstance(prong_matching, list):
            self._prong_matchings = []
            for pm in prong_matching:
                prong1, prong2 = pm
                (l1, c1, h1, a1) = prong1
                (l2, c2, h2, a2) = prong2

                l1 = self._check_level(l1)
                l2 = self._check_level(l2)
                if l2 <= l1:
                    raise ValueError(f"invalid prong matching; got l1={l1} and l2={l2}")

                if isinstance(h1, str):
                    h1 = str_to_label(h1)
                if isinstance(h2, str):
                    h2 = str_to_label(h2)

                vt1 = self._veering_triangulations[l1][c1]
                vt2 = self._veering_triangulations[l2][c2]

                h1, a1 = vt1._check_vertex_separatrix(h1, a1)
                h2, a2 = vt2._check_face_separatrix(h2, a2)

                # adjust prong2 according to our convention that we do not consider the last prong in the each corner
                h2, a2 = self._veering_triangulations[l2][c2]._normalize_face_separatrix(h2, a2)

                for (hh1, aa1), (hh2, aa2) in zip(vt1.vertex_separatrices(h1, a1), vt2.face_separatrices(h2, a2)):
                    if (hh1, aa1) < (h1, a1):
                        h1 = hh1
                        a1 = aa1
                        h2 = hh2
                        a2 = aa2

                pm = ((l1, c1, h1, a1), (l2, c2, h2, a2))
                if check:
                    self._check_local_prong_matching(pm)
                self._prong_matchings.append(pm)

            self._prong_matchings = sorted(self._prong_matchings)
        else:
            raise ValueError("The 'prong_matching' must be a list.")

        self._mutable = True
        if not mutable:
            self.set_immutable()

        if check:
            self._check_prong_matching()
            self._check_horizontal_residue_conditions()

    def _check(self):
        self._check_horizontal_residue_conditions()
        self._check_prong_matching()

    def _check_level(self, level):
        r"""
        Return a level as a positive integer
        """
        if not isinstance(level, numbers.Integral):
            raise TypeError("level must be integral")
        level = int(level)
        if level < 0:
            level = -level
        if not 0 <= level < self.num_levels():
            raise ValueError("level out of range")
        return level

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
        for level, nodes in enumerate(self._horizontal_nodes):
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
                        raise ValueError(f"distinct residues at horizontal node {(h1, h2)} at the {c}-th component at level-{level}")

    def _check_local_prong_matching(self, pm):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation, MultiscaleVeeringTriangulation

            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: pm = [(0, 0, 0,4),(-1, 0, 0, 1)]
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: angle (=4) out of range for separatrix at half_edge=0; must be >= 0 and < 4
            sage: pm = [(0,0,7,0),(1,0,0,1)]
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: angle (=0) out of range for separatrix at half_edge=7; must be >= 0 and < 0
            sage: pm = [((0,0,1,0),(1,0,0,1)]
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: The orders of the zero in (0, 0, 1, 0) and  the pole in (1, 0, 0, 1) are not matched
        """

        N = len(self._veering_triangulations)
        prong1, prong2= pm

        l1, c1, h1, a1 = prong1
        l2, c2, h2, a2 = prong2

        l1 = self._check_level(l1)
        l2 = self._check_level(l2)

        #check the levels are valid
        if l1 < 0 or l1 >= N or l2 < 0 or l2 >= N:
            raise ValueError(f"The levels in {pm} are invalid")
        if l1 >= l2:
            raise ValueError(f"The level of {prong1} should be greater than the level of {prong2}")

        vt1 = self._veering_triangulations[l1][c1]
        vt2 = self._veering_triangulations[l2][c2]

        #check the orders of the zero and pole are matched
        if vt2.face_angle(h2) == 0:
            raise ValueError(f"The prong {prong2} is contained in a face of simple pole")
        if (vt1.vertex_angle(h1) + vt2.face_angle(h2) != 0):
            raise ValueError(f"The orders of the zero in {prong1} and  the pole in {prong2} are not matched")

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
        pms = self._prong_matchings
        l1 = []
        l2 = []
        for pm in pms:
            p1, p2 = pm
            level1, c1, _, _ = p1
            level2, c2, _, _ = p2
            v, f = self.vertical_node(pm)
            if (level1, c1, v) in l1:
                raise ValueError(f"There are prongs at the same zero as {pm[0]}")
            else:
                l1.append((level1, c1, v))
            if (level2, c2, f) in l2:
                raise ValueError(f"There are prongs at the same pole as {pm[1]}")
            else:
                l2.append((level2, c2, f))

    def __str__(self):
        vt_strings = ",\n    ".join("[" + ", ".join(str(vt) for vt in l) + "]" for l in self._veering_triangulations)
        horizontal_nodes_str = "[" + ", ".join(str(hn) for hn in self._horizontal_nodes) + "]"
        prong_matching_str = "[" + ", ".join(str(pm) for pm in self._prong_matchings) + "]"
        return (
            f"MultiscaleVeeringTriangulation(\n"
            f"  veering_triangulations=[\n    {vt_strings}\n  ],\n"
            f"  horizontal_nodes={horizontal_nodes_str},\n"
            f"  prong_matching={prong_matching_str}\n"
            f")"
        )

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if type(self) != type(other):
            raise TypeError
        return (self._veering_triangulations == other._veering_triangulations) and (self._horizontal_nodes == other._horizontal_nodes) and (self._prong_matchings == other._prong_matchings)

    def __ne__(self, other):
        if type(self) != type(other):
            raise TypeError
        return self._veering_triangulations != other._veering_triangulations and self._horizontal_nodes != other._horizontal_nodes and self._prong_matchings != other._prong_matchings

    def copy(self, mutable=None):
        if mutable is None:
            mutable = self._mutable

        if not mutable and not self._mutable:
            return self

        ans = MultiscaleVeeringTriangulation.__new__(MultiscaleVeeringTriangulation)
        ans._veering_triangulations = [[vt.copy(mutable) for vt in vts] for vts in self._veering_triangulations]
        ans._horizontal_nodes = [[nodes[:] for nodes in hnodes] for hnodes in self._horizontal_nodes]
        ans._prong_matchings = self._prong_matchings[:]
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

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[f0, f1], [f2]], prong_matching=[[((0, 0), 0, 0), ((1, 0), 0, 0)], [((0, 1), 0, 0), ((1, 0), 4, 0)]], mutable=False)
            sage: hash(mvt) # random
            313904658927315188
            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[f0, f1], [f2]], prong_matching=[[((0, 0), 0, 0), ((1, 0), 0, 0)], [((0, 1), 0, 0), ((1, 0), 4, 0)]], mutable=True)
            sage: hash(mvt)
            Traceback (most recent call last):
            ...
            ValueError: mutable veering triangulation are not hashable
        """
        if self._mutable:
            raise ValueError("mutable veering triangulation are not hashable")
        veering_triangulations_hashable = tuple(tuple(vts) for vts in self._veering_triangulations)
        horizontal_nodes_hashable = tuple(tuple(tuple(comp) for comp in level) for level in self._horizontal_nodes)
        prong_matching_hashable = hash(tuple(self._prong_matchings))
        return hash((veering_triangulations_hashable, horizontal_nodes_hashable, prong_matching_hashable))

    def num_levels(self):
        return len(self._veering_triangulations)

    def permute_level(self, level, p):
        r"""
        Apply the permutation ``p`` on the components of level ``level``.

        EXAMPLES::

            sage: from veerer import *

            sage: f0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)])
            sage: f1 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
            sage: f2 = VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])

            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[f0, f1], [f2]], prong_matching=[[((0, 0), 0, 0), ((1, 0), 0, 0)], [((0, 1), 0, 0), ((1, 0), 4, 0)]], mutable=True)
            sage: mvt.permute_level(0, [1, 0])
            sage: mvt
            MultiscaleVeeringTriangulation(
              veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)])],
                [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
              ],
              horizontal_nodes=[[[], []], [[]]],
              prong_matching=[(((0, 0), 0, 0), ((1, 0), 4, 0)), (((0, 1), 0, 0), ((1, 0), 0, 0))]
            )
        """
        if not self._mutable:
            raise ValueError("immutable multiscale veering triangulation; use a multable copy instead")
        level = self._check_level(level)
        n = len(self._veering_triangulations[level])
        p = perm_init(p, n)
        perm_on_list(self._veering_triangulations[level], p, n)
        perm_on_list(self._horizontal_nodes[level], p, n)

        # permute prong matchings
        for i, (pm0, pm1) in enumerate(self._prong_matchings):
            (level0, comp0), h0, a0 = pm0
            (level1, comp1), h1, a1 = pm1
            if level0 == level:
                pm0 = ((level0, p[comp0]), h0, a0)
                self._prong_matchings[i] = (pm0, pm1)
            elif level1 == level:
                pm1 = ((level1, p[comp1]), h1, a1)
                self._prong_matchings[i] = (pm0, pm1)
        self._prong_matchings.sort()

        self._check()

    def horizontal_faces(self, level, c, node):
        r"""
        Return a pair of faces corresponding to the node
        """
        level = self._check_level(level)
        h1, h2 = node

        vt = self._veering_triangulations[level][c]

        return (perm_orbit(vt._fp, h1), perm_orbit(vt._fp, h2))

    def horizontal_nodes_at_level(self, level):
        r"""
        Return the list of horizontal nodes at the level of the input 'i'.

        Each node is represented by a triple (level,comp,face0,face1).

        EXAMPLES::
        """
        level = self._check_level(level)

        l = self._horizontal_nodes[level]
        list_horiz_nodes = []
        for comp, nodes in enumerate(l):
            for node in nodes:
                f0, f1 = self.horizontal_faces(level, comp, node)
                list_horiz_nodes.append((level, comp, f0, f1))

        return list_horiz_nodes

    def vertical_node(self, pm):
        r"""
        Return the underlying node of the prong matching, which is represented as a pair of zero and face
        """
        p1, p2 = pm
        l1, c1, h1, _ = p1
        l2, c2, h2, _ = p2
        l1 = self._check_level(l1)
        l2 = self._check_level(l2)
        vt1 = self._veering_triangulations[l1][c1]
        vt2 = self._veering_triangulations[l2][c2]
        for v in vt1.vertices():
            if h1 in v:
                v1 = v
        for f in vt2.boundary_faces():
            if h2 in f:
                f1 = f
        return (v1, f1)

    def _local_prong_matching(self, pm):
        r"""
        Returns the local prong matching at a vertical node.

        The input vertical node is represented by a tube (l1,v,l2,f), where v is the vertex of level-l1 veering triangulation, and f is the boundary face of level-l2 veering triangulation

        The output prong matching is represented as a list containing two sublists: [prongs1, prongs2].
        Each sublist 'prongsi' is a list of prongs, where each prong is represented as a tuple: (level, half_edge, angle_data).
        The angle_data specifies which prong within the corner of the half_edge is being referred to.
        Prongs with the same index in the two sublists are matched.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, MultiscaleVeeringTriangulation
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[[(0,0,"0",0),(-1,0,"0",1)],[(0,0,"2",0),(-1,0,"5",1)]])
            sage: mvt0._local_prong_matching([(0,0,0,0),(-1,0,0,1)])
            [[(0, 0), (0, 1), (0, 2), (0, 3)], [(0, 1), (0, 0), (0, 3), (0, 2)]]
        """
        ((l1, c1, h1, a1), (l2, c2, h2, a2)) = pm

        vt1 = self._veering_triangulations[l1][c1]
        vt2 = self._veering_triangulations[l2][c2]

        prongs1 = vt1.vertex_separatrices(h1, a1)
        prongs2 = vt2.face_separatrices(h2, a2)

        assert len(prongs1) == len(prongs2)
        return [prongs1, prongs2]

    def _components_have_horiztal_nodes_with(self, level, label, comp_index):
        r"""
        Return the indices of the connected components that have horizontal nodes with the input component at `label`-th component at level-`level`.
        """
        level = self._check_level(level)
        l_node = self.horizontal_nodes_at_level(level)

        l = []
        for level, s, f1, f2 in l_node:
            assert level >= 0
            #compute the connected component indices of the face f1 and f2
            vt = self._veering_triangulations[level][s]
            c1 = in_connected_component(vt, f1[0])
            c2 = in_connected_component(vt, f2[0])

            if (s, c1) == (label, comp_index):
                l.append((level, s, c2))
            if (s, c2) == (label, comp_index):
                if (level,s,c1) not in l:
                    l.append((level,s,c1))
        return l

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
            sage: mvt0 = MultiscaleVeeringTriangulation([vt0,vt1],[[""],["(~4,7)"]],[[(0,0,"0",0),(-1,0,"0",1)],[(0,0,"2",0),(-1,0,"5",1)]])
            sage: mvt0.is_abelian()
            False
            sage: vt2 = VeeringTriangulationLinearFamily("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(2:1)(~3:1)(~4:1)(5:5)(7:1)(~8:1)(~9:1)", "BBRBRBBRBR", [(1, 0, 0, 0, 1, 0, 0, 0, 0, 0), (0, 1, 0, 1, -1, 0, 0, 1, 1, 0), (0, 0, 1, 1, 0, 0, 0, 1, 1, 0), (0, 0, 0, 0, 0, 1, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, 1, -1, 0, -1)])
            sage: mvt1 = MultiscaleVeeringTriangulation([vt0,vt2],[[""],["(~3,~8)"]],[[(0,0,"0",0),(-1,0,"0",1)],[(0,0,"2",0),(-1,0,"5",1)]])
            sage: print(mvt1.is_abelian(certificate=True))
            (True, [[[True, False, True, False, False, True, False, True, False, True]], [[False, True, False, True, False, True, False, True, False, True, True, False, True, False, True, False, True, False, True, False]]])
        """
        N = self.num_levels()

        # Step1: compute orientations of components
        oris = []
        for i, vts in enumerate(self._veering_triangulations):
            oris.append([])
            for vt in vts:
                abelian, l = vt.is_abelian(certificate=True)
                if abelian:
                    oris[-1].append(l)
                else:
                    return (False, None) if certificate else False

        # Step2: propagate through horizontal nodes
        for i, vts in enumerate(self._veering_triangulations):
            l_component = []
            for vt in vts:
                l_component.append(vt.connected_components())

            l_nodes = self.horizontal_nodes_at_level(i)
            lc = [] # the list of components in the i-th level adjusted so far
            for level, s, f1, f2 in l_nodes:
                # find out the connected components containing the matched poles
                vt = self._veering_triangulations[level][s]

                c1 = in_connected_component(vt, f1[0])
                c2 = in_connected_component(vt, f2[0])

                lo = oris[i][s]
                ne = len(lo)

                if lo[f1[0]] == lo[f2[0]]:
                    # check coherence
                    if c1 == c2:
                        return (False, None) if certificate else False

                    if ((s,c1) in lc) and ((s,c2) in lc):
                        return (False, None) if certificate else False

                    if (s,c1) not in lc:
                        # rotate the component c1 by pi
                        for h in range(ne):
                            if h // 2 in l_component[s][c1]:
                                lo[h] = not lo[h]
                        # add coherent components
                        lc.append((s,c1))
                        if (s, c2) not in lc:
                            lc.append((s,c2))
                    elif (s, c2) not in lc:
                        # rotate the component c2 by pi
                        for h in range(ne):
                            if h // 2 in l_component[s][c2]:
                                lo[h] = not lo[h]
                        lc.append((s, c2))
                else:
                    # add coherent components
                    if (s, c1) not in lc:
                        lc.append((s, c1))
                    if (s, c2) not in lc:
                        lc.append((s, c2))

                oris[i][s] = lo

        #Step3: propagate through vertical nodes

        lv = [] #the list of component adjusted so far, where the component is labeled by (level, index of the component in this level)

        for pm in self._prong_matching:

            level1, s1, h1, ang1 = pm[0]
            level2, s2, h2, ang2 = pm[1]
            assert level1 >= 0 and level2 >= 0

            vt1 = self._veering_triangulations[level1][s1]
            vt2 = self._veering_triangulations[level2][s2]

            o1 = oris[level1][s1][h1]
            o2 = oris[level2][s2][h2]

            # decide the orientation of the prong pm[0]
            if ang1 % 2 == 1:
                o1 = not o1

            # decide the orientation of the prong pm[1]
            if ang2 % 2 == 1:
                o2 = not o2

            # find the labels of the components where the prongs are.
            # the labels are in the form: (level, index of the component in this level)
            # moreover find out all the components that have horizontal nodes with the components containing the prongs
            c1 = in_connected_component(vt1, h1)
            l1 = self._components_have_horiztal_nodes_with(level1, s1, c1)
            if (level1, s1, c1) not in l1:
                l1.append((level1, s1, c1))

            c2 = in_connected_component(vt2, h2)
            l2 = self._components_have_horiztal_nodes_with(level2, s2, c2)
            if (level2, s2, c2) not in l2:
                l2.append((level2, s2, c2))

            # adjust components
            lo1 = oris[level1][s1]
            n1 = len(lo1)
            lo2 = oris[level2][s2]
            n2 = len(lo2)
            if o1 != o2: # incoherent orientations
                if ((level1,s1, c1) in lv) and ((level2, s2, c2) in lv):
                    return (False, None) if certificate else False

                if (level1, s1, c1) not in lv:
                    #rotate all the components in l1 by pi
                    for h in range(n1):
                        c = in_connected_component(vt1, h)
                        if (level1, s1, c) in l1:
                            lo1[h] = not lo1[h]

                        for label in l1:
                            lv.append(label)

                        if (level2, s2, c2) not in lv:
                            for label in l2:
                                lv.append(label)

                elif (level2,s2, c2) not in lv:
                    #rotate all the components in l2 by pi
                    for h in range(n2):
                        c = in_connected_component(vt2, h)
                        if (level2, s2, c) in l2:
                            lo2[h] = not lo2[h]

                        for label in l2:
                            lv.append(label)
            else: # coherent orientation
                if (level1, s1, c1) not in lv:
                    for label in l1:
                        lv.append(label)
                if (level2, s2, c2) not in lv:
                    for label in l2:
                        lv.append(label)

            oris[level1][s1] = lo1
            oris[level2][s2] = lo2

        return (True, oris) if certificate else True

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
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[""],[""]],[[(0,0,"0",0),(-1,0,"0",1)],[(0,0,"2",0),(-1,0,"5",1)]])
            sage: mvt0.degeneration(-1,0, edges_low=[0, 1, 2, 3, 4, 5], edges_up=[6, 7])
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)", "RBRBB")],
                [VeeringTriangulationLinearFamily("(~0,1,2)(~1,~2,3)(0:5)(~3:1)(4:4,5:4)(~4:1)(~5:1)", "BBRBBB", [(1, 0, 1, 1, 0, 0), (0, 1, -1, 0, 0, 0), (0, 0, 0, 0, 1, 1)])]
            ],
            horizontal_nodes=[[[]], [[(9, 11)]]],
            prong_matching=[[(0, 0, 0, 0), (1, 0, 0, 1)], [(0, 0, 4, 0), (1, 0, 10, 1)]]
            )
        """
        level = self._check_level(level)

        vts = copy.deepcopy(self._veering_triangulations)
        vt = vts[level][component]
        nh = 2 * (vt.num_edges())
        ep = vt.edge_permutation()

        f_up ,f_low, r_up, r_low = vt.degeneration(edges_low=edges_low, edges_up=edges_up, collapsed_half_edge_relabelling=True)

        #build list of veering triangulations.
        #TO BE CONFIRMED: there are choices of the component in the original level ``level`` in the new levels. However, since we will consider all possible vertical degenerations, we could consider just one case that their levels remain the same.

        if f_up is None:
            vts[level][component] = f_low
        else:
            vts[level][component] = f_up
            vts.insert(level + 1, [f_low])

        # build the horizontal nodes.
        l1 = [] #new horizontal nodes at (level, component)
        l2 = [] #new horizontal nodes at (level - 1, 0) if the degeneration has two levels
        l_horiz = copy.deepcopy(self._horizontal_nodes)

        # existing horizontal nodes
        for h1, h2 in self._horizontal_nodes[level][component]:
            if r_up[h1] >= 0:
                h1 = r_up[h1]
                h2 = r_up[h2]
                assert h2 >= 0
                l1.append((h1, h2))
            else:
                h1 = r_low[h1]
                h2 = r_low[h2]
                assert h1 >= 0
                assert h2 >= 0
                if f_up is None:
                    l1.append((h1, h2))
                else:
                    l2.append((h1, h2))

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
        original_pm = copy.deepcopy(self._prong_matchings)
        for pm in original_pm:
            prong1, prong2 = pm
            if prong1[0] == level and prong1[1] == component:
                prong1 = track_prong(vt, r_up, r_low, prong1)
                if f_up is None:
                    l_pm.append([prong1, prong2])
                else:
                    prong2 = (prong2[0] + 1,prong2[1], prong2[2], prong2[3])
                    l_pm.append([prong1,prong2])
            elif prong2[0] == level and prong2 == component:
                prong2 = track_prong(vt, r_up, r_low, prong2)
                l_pm.append([prong1,prong2])
            else:
                l_pm.append(pm)
        #new vertical nodes
        if f_up is not None:
            l_pm  = l_pm + _new_prong_matching(vt, f_low, r_up, r_low, level, component)

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

            sage: vt = VeeringTriangulation("(~0,2,3)(~1,4,5)(~2,6,7)(~3,~5,8)(~4,9,10)(~6,11,12)(~7,13,14)(~8,~12,15)(~9,16,~15)(~11,17,18)(~14,~18,19)(~16,~17,20)(0:1)(1:1)(~10:1)(~13:1)(~19:1)(~20:1)", "BBRRRBBBRBBRRBRBRRBBB")
            sage: f = vt.add_residue_constraints([[1,-1,0,0,0,0],[0,0,1,-1,0,0],[0,0,0,0,1,-1]])
            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[f], horizontal_nodes=[[[(0, 2), (21, 27), (39, 41)]]], prong_matching=[])
            sage: for mvt2 in mvt.codimension_one_vertical_degenerations():
            ....:     print(mvt2)
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

    def transport_along_path(self, level, component, path):
        r"""
        Return the multi-scale Veering triangulation obtained by deforming the prime veering triangulation at ``(level, component)`` along the path in the Delaunay-Strebel graph.

        EXAMPLES::

            sage: from veerer import *

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "RRBBRRRRBBBR")
            sage: edges_up = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
            sage: mvt0 = MultiscaleVeeringTriangulation([vt], [[""]], [])
            sage: mvt = mvt0.degeneration(0,0,edges_up=edges_up)
            sage: mvt
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRRRRB", [(1, 0, -1, -1, 0, -1, -1, 0, 1), (0, 1, 1, 1, 0, 1, 1, 0, -1), (0, 0, 0, 0, 1, 1, 1, 0, -1), (0, 0, 0, 0, 0, 0, 0, 1, 1)])],
                [VeeringTriangulationLinearFamily("(0:4,~0:4)", "R", [(1)])]
            ],
            horizontal_nodes=[[[]], [[]]],
            prong_matching=[((0, 0, 0, 0), (1, 0, 0, 1))]
            )
            sage: vt0 = mvt._veering_triangulations[0][0]
            sage: ds_graph = vt0.delaunay_strebel_graph()
            sage: path = ds_graph.path(0, [3, 13, 16])
            sage: mvt.transport_along_path(0, 0, path)
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BRBBRRRBR", [(1, 0, 1, 1, 0, 1, 1, 0, 1), (0, 1, 1, 1, 0, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 0, 0, 0, 1, -1)])],
                [VeeringTriangulationLinearFamily("(0:4,~0:4)", "R", [(1)])]
            ],
            horizontal_nodes=[[[]], [[]]],
            prong_matching=[(((0, 0), 2, 0), ((1, 0), 0, 1))]
            )
        """
        level = self._check_level(level)

        ds_graph = path._graph
        vt0 = ds_graph.vertex_label(path.start())
        vt1 = ds_graph.vertex_label(path.end())
        assert self._veering_triangulations[level][component] == vt0

        vts = copy.deepcopy(self._veering_triangulations)
        vts[level][component] = vt1

        mono = SeparatrixMonodromy(ds_graph)

        #new horizontal nodes
        l1 = [] #new horizontal nodes at (level, component)
        l_horiz = copy.deepcopy(self._horizontal_nodes)
        for h1, h2 in l_horiz[level][component]:
            h1 = mono.infinite_cylinder_transport(path, h1)
            h2 = mono.infinite_cylinder_transport(path, h2)
            l1.append((h1,h2))
        l_horiz[level][component] = l1
        
        #new vertical nodes
        l2 = []
        l_vert = copy.deepcopy(self._prong_matchings)
        for pm in l_vert:
            p1, p2 = pm
            level1, c1, h1, ang1 = p1
            level2, c2, h2, ang2 = p2
            if level1 == level and c1 == component:
                h1, ang1 = mono.vertex_separatrix_transport(path, h1, ang1)
            if level2 == level and c2 == component:
                h2, ang2 = mono.face_separatrix_transport(path, h2, ang2)
            assert level1 >= 0 and level2 >= 0
            l2.append([(level1, c1, h1, ang1),(level2, c2, h2, ang2)])
        l_vert = l2

        return MultiscaleVeeringTriangulation(vts,l_horiz,l_vert)

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
            prong_matching=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 10, 0), (1, 0, 4, 0))]
            )
            sage: mvt1.prime_decomposition(0, 0)
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])],
                [VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])]
            ],
            horizontal_nodes=[[[], []], [[]]],
            prong_matching=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 1, 0, 0), (1, 0, 4, 0))]
            )
        """
        level = self._check_level(level)
        vts = copy.deepcopy(self._veering_triangulations)
        vt = vts[level][component]

        l = copy.deepcopy(vt.prime_decomposition())

        #store the prime component and mapping to the canonical labels
        l_comp = []
        l_vts_canonical = []
        l_mapping = []

        for prime in l:
            l_comp.append(prime[0])

            vt_prime = copy.deepcopy(prime[1])
            vt_prime._mutable = True
            mapping = vt_prime.set_canonical_labels(mapping=True)
            vt_prime.set_immutable()

            l_vts_canonical.append(vt_prime)
            l_mapping.append(mapping)

        #build veering triangulations
        vts[level][component : component + 1] = l_vts_canonical

        def label_in_prime_comp(h, l_comp, l_mapping):
            for edges in l_comp:
                if h // 2 in edges:
                    c = l_comp.index(edges)
                    mapping = l_mapping[c]
                    i = edges.index(h // 2)
                    if h%2 == 0:
                        return (c, mapping[2 * i])
                    else:
                        return (c, mapping[2 * i + 1])

        #new horizontal nodes
        l1 = [[] for i in range(len(l))]
        l_horiz = copy.deepcopy(self._horizontal_nodes)
        for h1, h2 in l_horiz[level][component]:
            cp1, h1 = label_in_prime_comp(h1, l_comp, l_mapping)
            cp2, h2 = label_in_prime_comp(h2, l_comp, l_mapping)
            assert cp1 == cp2
            l1[cp1].append((h1,h2))
        l_horiz[level][component:component + 1] = l1

        #new vertical nodes
        l2 = []
        l_vert = copy.deepcopy(self._prong_matchings)
        for pm in l_vert:
            p1, p2 = pm
            level1, c1, h1, ang1 = p1
            level2, c2, h2, ang2 = p2
            if (level1, c1) == (level, component):
                cp1, h1 = label_in_prime_comp(h1, l_comp, l_mapping)
                p1 = (level, cp1 + component, h1, ang1)
            if (level2, c2) == (level, component):
                cp2, h2 = label_in_prime_comp(h2, l_comp, l_mapping)
                p2 = (level, cp2 + component, h2, ang2)
            if level1 == level and c1 > component:
                p1 = (level, c1 + len(l_vts_canonical) - 1, h1, ang1)
            if level2 == level and c2 > component:
                p2 = (level, c2 + len(l_vts_canonical) - 1, h2, ang2)
            l2.append([p1,p2])
        l_vert = l2

        return MultiscaleVeeringTriangulation(vts,l_horiz,l_vert)

    def transport_by_monodromy(self, lc, ld):
        r"""
        Return a list of multi-scale veering triangulations that is obtained by the actions of the monodromy of the Delaunay-Strebel graph in the list ``ld`` on the input multi-scale veering triangulation.

        Input:
        - lc is a list of indicise of components of the multi-scale Veering triangulation, and each index is given by (level, component index).
        - ld is a list of Delaunay-Strebel graphs corresponding to the components in lc.

        EXAMPLES:

        """
        raise NotImplementedError

        from itertools import product
        l_g = [] #list of monodromy groups
        for dsg in ld:
            monog = dsg.framing_group()
            l_g.append(list(monog))

            vertex_separatrices = vt.vertex_separatrices(flat=True)
            vertex_separatrix_index = {ha: i for i, ha in enumerate(vertex_separatrices)}
            nv = len(vertex_separatrices)

            face_separatrices = vt.face_separatrices(flat=True)
            face_separatrix_index = {ha: nv + i for i, ha in enumerate(face_separatrices)}
            nf = len(face_separatrices)

            infinite_cylinders = [min(f) for f in vt.boundary_faces() if vt.face_angle(f[0]) == 0]
            infinite_cylinder_index = {h: nv + nf + i for i, h in enumerate(infinite_cylinders)}
            nc = len(infinite_cylinders)

            n = nv + nf + nc

            l_info.append((vertex_separatrices, vertex_separatrix_index, face_separatrices, face_separatrix_index, infinite_cylinders, infinite_cylinder_index, nv, nf, nc, n))

            monog0 = dsg.monodromy()
            monog = [perm_init(f"{p}", n=n) for p in monog0]
            l_g.append(monog)

        from itertools import product
        G = product(*l_g)
        lmvts = set()
        for g in G:
            
            per = [ld[i].framing_group_element_permutation(g[i]) for i in range(len(lc))]
            
            #do not change veering triangulations
            vts = copy.deepcopy(self._veering_triangulations)

            #new horizontal nodes
            l_horiz = copy.deepcopy(self._horizontal_nodes)
            for (level, c) in lc:
                i = lc.index((level, c))
                l1 = []
                for h1, h2 in l_horiz[level][c]:
                    h1 = per[i][2][h1]
                    h2 = per[i][2][h2]
                    assert h1 == min(perm_orbit(vts[level][c]._fp, h1)) and h2 == min(perm_orbit(vts[level][c]._fp, h2)) 
                    l1.append((h1, h2))
                l_horiz[level][c] = l1

            #new vertical nodes
            l2 = []
            l_vert = copy.deepcopy(self._prong_matchings)
            for pm in l_vert:
                p1, p2 = pm
                level1, c1, h1, ang1 = p1
                level2, c2, h2, ang2 = p2

                if (level1, c1) in lc:#the zero of the node is contained in the component
                    i = lc.index((level1, c1))
                    assert (ang1 == 0) and (h1 == min(perm_orbit(vts[level1][c1]._vp, h1))) #check that the data is normalized 
                    h1, ang1 = per[i][0][h1, ang1]
                if (level2, c2) in lc: #the pole of the node is contained in the component
                    i = lc.index((level2, c2))
                    h2, ang2 = per[i][1][h2, ang2]
                l2.append([(level1, c1, h1, ang1),(level2, c2, h2, ang2)])
            l_vert = l2
            mvtnew = MultiscaleVeeringTriangulation(vts,l_horiz,l_vert)
            lmvts.add(mvtnew)
        return list(lmvts)

    def transport_by_permutation_in_levels(self):
        r"""
        Return the list of multi-scale veering triangulations by permutes the same components in each level.

        EXAMPLES::
            
            sage: vt = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
            sage: vt1 = VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
            sage: veering_triangulations = [[vt, vt], vt1]
            sage: mvt  = MultiscaleVeeringTriangulation(veering_triangulations, horizontal_nodes=[[[], []], [[]]], prong_matching=[[(0, 0, 0, 0), (1, 0, 0, 0)], [(0, 1, 0, 0), (1, 0, 4, 0)]])
            sage: mvt.transport_by_permutation_in_levels()
            [MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]),
                VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
            ],
            horizontal_nodes=[[[], []], [[]]],
            prong_matching=[[(0, 0, 0, 0), (1, 0, 0, 0)], [(0, 1, 0, 0), (1, 0, 4, 0)]]
            ),
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]),
                VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
            ],
            horizontal_nodes=[[[], []], [[]]],
            prong_matching=[[(0, 0, 0, 0), (1, 0, 4, 0)], [(0, 1, 0, 0), (1, 0, 0, 0)]]
            )]
        """
        N = self.num_levels()

        #generate the level-wise permutation groups:
        l_g = []
        for i in range(N):
            vts = self._veering_triangulations[i]
            #find the same components
            labels = []
            label_map = {}
            k = -1
            for vt in vts:
                if vt not in label_map:
                    k += 1
                    label_map[vt] = k
                labels.append(label_map[vt])
            #generate the symmetry group
            m = max(labels)
            generators = []
            for i in range(m + 1):
                indices = [idx for idx, label in enumerate(labels) if label == i]
                generators.extend([(indices[k], indices[k + 1]) for k in range(len(indices) - 1)])
            n = len(vts)
            S = SymmetricGroup(range(n))
            g = S.subgroup([S(a) for a in generators])
            array_g = [perm_init(f"{p}", n=n) for p in g]
            l_g.append(array_g)

        from itertools import product
        G = product(*l_g)
        mvts = []
        for p in G:
            new_vts = copy.deepcopy(self._veering_triangulations)

            #new horizontal nodes
            orig_horiz_nodes = copy.deepcopy(self._horizontal_nodes)
            new_horiz_nodes = [None] * N
            for i in range(N):
                level_horiz = orig_horiz_nodes[i]
                new_horiz_nodes[i] = [None] * len(new_vts[i])
                assert len(level_horiz) == len(new_horiz_nodes[i])
                g = p[i] #permutation at level-i
                for j in range(len(new_vts[i])):
                    new_horiz_nodes[i][g[j]] = level_horiz[j]

            #new prong-matchings
            orig_pms = copy.deepcopy(self._prong_matchings)
            new_pms = []
            for p1, p2 in orig_pms:
                l1, c1, h1, ang1 = p1
                l2, c2, h2, ang2 = p2
                assert l1 >= 0 and l2 >= 0
                new_pms.append([(l1, p[l1][c1], h1, ang1), (l2, p[l2][c2], h2, ang2)])

            mvts.append(MultiscaleVeeringTriangulation(new_vts, new_horiz_nodes, new_pms))

        return mvts

    def codimension_one_vertical_prime_degenerations(self, level, component, ind_ds_graph, D, index=False):
        r"""
        Return a list of lists of multi-scale veering triangulations obtained
        by codimension-one vertical degenerations of the component.

        The returned list is organized as `l = [l0, l1, ...]`, where each Each sublist li satisfies that:
        - li contains multi-scale veering triangulations with the same enhanced level graph.
        - The corresponding components of the triangulations in li belong to the same cell of veering triangulations.
        - The triangulations in li are in the same connected component of the linear subvariety.

        Input:
        - `ds_graph`: The index of the Delaunay-Strebel graph of the prime component (which is the `component`-th component at the `level`).
        - `D`: An instance of the `PrimeDegeneration` class, responsible for computing the codimension-one vertical degenerations
        of the `component` in `ds_graph`.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.linear_subvariety import *
            sage: from veerer.labelled_digraph import *
            sage: from veerer.monodromy import *

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "RRBBRRRRBBRR")
            sage: mvt = MultiscaleVeeringTriangulation([vt], [[""]], [])
            sage: D = PrimeDegenerations()
            sage: ds_graph = vt.delaunay_strebel_graph()
            sage: l1 = D.codimension_one_vertical_degenerations(ds_graph)
            sage: D.find(ds_graph)
            0
            sage: lmvt1 = mvt.codimension_one_vertical_prime_degenerations(0, 0, 0, D)  # not tested
            sage: mvt1 = lmvt1[0][0]  # not tested
            sage: vt0 = mvt1._veering_triangulations[0][0]  # not tested
            sage: ds_graph0 = vt0.delaunay_strebel_graph()  # not tested
            sage: l2 = D.codimension_one_vertical_degenerations(ds_graph0)  # not tested
            sage: D.find(ds_graph0)  # not tested
            2
            sage: lmvt2 = mvt1.codimension_one_vertical_prime_degenerations(0, 0, 2, D)  # not tested
            sage: mvt2 = lmvt2[0][0]  # not tested
            sage: mvt2._veering_triangulations  # not tested
            [[VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])],
            [VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)])],
            [VeeringTriangulationLinearFamily("(0:4,~0:4)", "R", [(1)])]]
            sage: l2[0]  # not tested
            ((Delaunay-Strebel graph of VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]) made of
                2 veering Delaunay states
                0 Strebel states
                4 flip transitions
                0 rotation transitions
                0 Strebel transitions,),
            (Delaunay-Strebel graph of VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)]) made of
                9 veering Delaunay states
                1 Strebel states
                8 flip transitions
                5 rotation transitions
                5 Strebel transitions,))
        """

        level = self._check_level(level)

        vt = self._veering_triangulations[level][component]
        ds_graph = D._components[ind_ds_graph]

        assert vt.is_prime()
        assert vt == ds_graph.root() #it is required to be the root of the Delaunay Strebel graph

        l = D._vertical_degenerations[ind_ds_graph]

        list_comps_after_degen = list(l.keys())

        llmvt = []
        lindex = []
        for list_comp_up, list_comp_low in list_comps_after_degen:
            l_vt_edge = l[(list_comp_up, list_comp_low)]#the list of (vt, edges_up, edges_low) such that vt degenerates to prime components in list_com_yp and list_comp_low respectively.
            l_ds_g_up = [D._components[index] for index in list_comp_up]
            l_ds_g_low = [D._components[index] for index in list_comp_low]
            lc0 = [(level, component + index) for index in range(len(list_comp_up))]
            lc1 = [(level + 1, index) for index in range(len(list_comp_low))]
            lc = lc0 + lc1
            ld = l_ds_g_up + l_ds_g_low

            #construct paths
            target_vertices = [ds_graph.vertex_index(a[0]) for a in l_vt_edge]
            paths = tree_with_target(ds_graph, root=0, target_vertices=target_vertices)
            assert len(paths) == len(l_vt_edge)

            #transport mvt
            lmvt = [self.transport_along_path(level, component, path) for path in paths]
            assert len(lmvt) == len(l_vt_edge)

            #make vertical degeneration and compute all transitions under monodromy groups and level-wise permutations
            l_deg_connected_comps = []
            all_mvt = []
            for i, mvt in enumerate(lmvt):
                _, edges_up, edges_low = l_vt_edge[i]
                mvt = mvt.degeneration(level, component, edges_low=edges_low, edges_up=edges_up)
                mvt = mvt.prime_decomposition(level, component)
                mvt = mvt.prime_decomposition(level + 1, 0)

                if mvt not in all_mvt:
                    l_mono = mvt.transport_by_monodromy(lc, ld)
                    new_connected_comp = []
                    for mvt1 in l_mono:
                        new_connected_comp = new_connected_comp + mvt1.transport_by_permutation_in_levels()
                    l_deg_connected_comps.append(new_connected_comp)
                    all_mvt = all_mvt + new_connected_comp
                    lindex.append([list(list_comp_up), list(list_comp_low)])

            llmvt = llmvt + l_deg_connected_comps

        return llmvt if not index else (llmvt, lindex)

    def codimension_one_horizontal_prime_degenerations(self, level, component, ind_ds_graph, D, index=False):
        r"""
        Return a list of lists of multi-scale veering triangulations obtained
        by codimension-one horizontal degenerations of the component.

        The returned list is organized as `l = [l0, l1, ...]`, where each Each sublist li satisfies that:
        - li contains multi-scale veering triangulations with the same enhanced level graph.
        - The corresponding components of the triangulations in li belong to the same cell of veering triangulations.
        - The triangulations in li are in the same connected component of the linear subvariety.

        Input:
        - `ds_graph`: The index of the Delaunay-Strebel graph of the prime component (which is the `component`-th component at the `level`).
        - `D`: An instance of the `PrimeDegeneration` class, responsible for computing the codimension-one horizontal degenerations
        of the `component` in `ds_graph`.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.linear_subvariety import *
            sage: from veerer.labelled_digraph import *
            sage: from veerer.monodromy import *

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "RRBBRRRRBBRR")
            sage: mvt = MultiscaleVeeringTriangulation([vt], [[""]], [])
            sage: D = PrimeDegenerations()
            sage: ds_graph = vt.delaunay_strebel_graph()
            sage: l1 = D.codimension_one_vertical_degenerations(ds_graph)
            sage: D.find(ds_graph)
            0
            sage: mvt1 = mvt.codimension_one_vertical_prime_degenerations(0, 0, 0, D)[0][0]  # not tested
            sage: vt0 = mvt1._veering_triangulations[0][0]  # not tested
            sage: ds_graph0 = vt0.delaunay_strebel_graph()  # not tested
            sage: l2 = D.codimension_one_vertical_degenerations(ds_graph0)  # not tested
            sage: D.find(ds_graph0)  # not tested
            2
            sage: mvt2 = mvt1.codimension_one_vertical_prime_degenerations(0, 0, 2, D)[0][0]  # not tested
            sage: vt1 = mvt2._veering_triangulations[1][0]  # not tested
            sage: ds_graph1 = vt1.delaunay_strebel_graph()  # not tested
            sage: l3 = D.codimension_one_horizontal_degenerations(ds_graph1)  # not tested
            sage: D.find(ds_graph1)  # not tested
            8
            sage: lmvts = mvt2.codimension_one_horizontal_prime_degenerations(-1, 0, 8, D)[0][2]  # not tested
        """

        level = self._check_level(level)

        vt = self._veering_triangulations[level][component]
        ds_graph = D._components[ind_ds_graph]
        assert vt.is_prime()
        assert vt == ds_graph.root() #it is required to be the root of the Delaunay Strebel graph

        l = D._horizontal_degenerations[ind_ds_graph]

        list_comps_after_degen = list(l.keys())

        llmvt = []
        lindex = []
        for list_comp in list_comps_after_degen:
            l_vt_edge = l[list_comp]
            l_ds_g = [D._components[index] for index in list_comp]
            
            lc = [(level, component + index) for index in range(len(list_comp))]
            ld = l_ds_g

            #construct paths
            target_vertices = [ds_graph.vertex_index(a[0]) for a in l_vt_edge]
            paths = tree_with_target(ds_graph, root=0, target_vertices=target_vertices)
            assert len(paths) == len(l_vt_edge)

            #transport mvt
            lmvt = [self.transport_along_path(level, component, path) for path in paths]
            assert len(lmvt) == len(l_vt_edge)

            #make vertical degeneration and compute all transitions under monodromy groups and level-wise permutations
            l_deg_connected_comps = []
            all_mvt = []

            for i, mvt in enumerate(lmvt):
                _, edges_up, edges_low = l_vt_edge[i]
                mvt = mvt.degeneration(level, component, edges_low=edges_low, edges_up=edges_up)
                mvt = mvt.prime_decomposition(level, component)
                
                if mvt not in all_mvt:
                    l_mono = mvt.transport_by_monodromy(lc, ld)
                    new_connected_comp = []
                    for mvt1 in l_mono:
                        new_connected_comp = new_connected_comp + mvt1.transport_by_permutation_in_levels()
                    l_deg_connected_comps.append(new_connected_comp)
                    all_mvt = all_mvt + new_connected_comp
                    lindex.append([list(list_comp)])

            llmvt = llmvt + l_deg_connected_comps

        return llmvt if not index else (llmvt, lindex)


def multiscale_compactification_representatives(L, D, index=False):
    r"""
    Return all connected components of the boundary in the multiscale compoactification of L as a dictionary.

    The value of the key `(i,j)` is a list [l0, l1, ....], where:
    - li is a list of multi-scale veering triangulations in the same connected components.
    - A triangulation in a list has `i` levels and `j` horizontal nodes.

    INPUT:
    - L: a prime linear family
    - D: An instance of the `PrimeDegeneration` class, responsible for computing all the degenerations of L

    EXAMPLES::

        sage: from veerer import *
        sage: from veerer.linear_subvariety import *
        sage: from veerer.labelled_digraph import *
        sage: from veerer.monodromy import *

        sage: vt = VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,8,~7)(~1,~8,3)(2,7,~6)(~2,~3,4)", "RRRBBBBBB")

    We compare two computations in the following. We first compute by using the class MultiscaleCompactification::

        sage: L = vt.linear_subvariety()  # not tested
        sage: M = L.multiscale_compactification()  # not tested
        sage: M  # not tested
        MultiscaleCompactification of Irreducible real linear subvariety of projective dimension 3 in [[H_2(2)]] made of
        3 components in codimension 1
        5 components in codimension 2
        3 components in codimension 3

    Then we compute by the method multiscale_compactification_representatives::

        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: D = PrimeDegenerations()
        sage: D.add(ds_graph)  # not tested
        0
        sage: D.compute_all()  # not tested
        sage: dic= multiscale_compactification_representatives(vt, D)  # not tested
        sage: print(f"{len(dic[1,0]) + len(dic[0,1])} components in codimension 1\n{len(dic[2,0]) + len(dic[1,1]) + len(dic[0,2])} components in codimension 2\n{len(dic[1,2]) + len(dic[2,1])} components in codimension 3")  # not tested
        3 components in codimension 1
        13 components in codimension 2
        14 components in codimension 3
    """
    assert L.is_prime()
    #mvt = mvt.prime_decomposition(0,0)

    ds_graph = L.delaunay_strebel_graph()
    L = ds_graph.root() #move to root
    mvt = MultiscaleVeeringTriangulation([L], [[""]], [])

    l = collections.defaultdict(list)
    l[0, 0].append([mvt])
    lindex = collections.defaultdict(list)
    ind = D.find(ds_graph) #find the initial index
    lindex[0, 0].append([[ind,]])

    all_mvt = []
    d = L.dimension()
    # vertical degenerations
    for codim in range(d - 1):
        for i, connected_comp in enumerate(l[codim, 0]):
            ind_comp = lindex[codim, 0][i] #the index of the components of the triangulations in connected_comp
            for mvt in connected_comp:
                #only degenerate the top level
                for comp in range(len(mvt._veering_triangulations[0])):
                    ind = ind_comp[0][comp] #the index of the comp
                    if len(D._vertical_degenerations[ind]) > 0:
                        l_mvts, inds = mvt.codimension_one_vertical_prime_degenerations(0, comp, ind, D, index=True)
                        for j, mvts in enumerate(l_mvts):
                            if mvts[0] not in all_mvt:
                                assert all(mvt not in all_mvt for mvt in mvts)
                                l[codim + 1, 0].append(mvts)
                                new = copy.deepcopy(ind_comp)
                                new[1:1] = [inds[j][1]]
                                new[0][comp:comp + 1] = inds[j][0]
                                lindex[codim + 1, 0].append(new)
                                all_mvt = all_mvt + mvts

    #horizontal degenerations
    for codim in range(d):
        h = 0
        has_horiz = True
        while has_horiz:
            has_horiz = False
            for i, connected_comp in enumerate(l[codim, h]):
                ind_comp = lindex[codim, h][i] #the index of the components of the triangulations in connected_comp
                for mvt in connected_comp:
                    N = mvt.num_levels()
                    for level in range(N):
                        for comp in range(len(mvt._veering_triangulations[level])):
                            ind = ind_comp[abs(level)][comp] #the index of the comp
                            if len(D._horizontal_degenerations[ind]) >0:
                                l_mvts, inds = mvt.codimension_one_horizontal_prime_degenerations(-abs(level), comp, ind, D, index=True)
                                for j, mvts in enumerate(l_mvts):
                                    if mvts[0] not in all_mvt:
                                        assert all(mvt not in all_mvt for mvt in mvts)
                                        l[codim, h + 1].append(mvts)
                                        new = copy.deepcopy(ind_comp)
                                        new[abs(level)][comp:comp + 1] = inds[j][0]
                                        lindex[codim, h + 1].append(new)
                                        all_mvt = all_mvt + mvts
                                        has_horiz = True
            h = h + 1

    return l if not index else (l, lindex)
