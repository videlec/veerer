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


def str_to_label(h):
    r"""
    Turn a string into the label of the half-edge
    """
    if h[0] == '~':
        lh = 2*int(h[1:]) + 1
    else:
        lh = 2*int(h[0:])
    return lh

def _num_vertical_separatrices_in_corner(vt, halfedge):
    r"""
    Return the times of red-blue colouring changes in the corner of the half-edge.

    The method is only used to boundary half-edges.
    """

    col = vt._colouring
    h1 = vt.vertex_permutation()[halfedge]
    a = vt.boundary_vector()[halfedge]

    if (col[halfedge // 2] == RED) and (col[h1 // 2] == BLUE):
        num = a + 1
    else:
        num = a

    return num

def in_connected_component(vt, h):
    r"""
    Return the index of the component which contains the half-edge h in the list vt.connected_components()
    """
    l_comp = vt.connected_components()
    for comp in l_comp:
        if (h // 2) in comp:
            return l_comp.index(comp)

def track_prong(vt, r_up, r_low, prong):

    m, h, ang = prong

    for v in vt.vertices():
        if h in v:
            v1 = v
    vh = [r_up[h] for h in v1]

    if min(vh) >= 0: #The case that vh is in f_up
        h = r_up[h]
        return (m, h, ang)
    else: #The case that vh is in f_low
         if max(r_up) == -1:
            return (m, r_low[h],ang)
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
            return ((m[0] - 1,0), r_low[h], ang)

def _vaninshing_red_blue_corner(vt, r_up, r_low, h):
    hh = vt.next_at_vertex(h)
    if r_up[h] >= 0 and r_low[hh] >= 0 and vt.boundary_vector()[h] == 0 and _num_vertical_separatrices_in_corner(vt, h) == 1:
        return True
    else:
        return False

def _new_prong_matching(vt, f_low, r_up, r_low, level, comp):

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
                while ((_num_vertical_separatrices_in_corner(vt, h) == 0) and (r_up[h] >= 0)) or (_vaninshing_red_blue_corner(vt, r_up, r_low, h)):
                    h = vt.previous_at_vertex(h)
                if (_num_vertical_separatrices_in_corner(vt, h) > 0) and (r_up[h] >= 0):
                    vert_sep = ((-abs(level), comp), h, 0)
                    prong1 = ((-abs(level),comp), r_up[h], 0)
                    prong2 = track_prong(vt, r_up, r_low, vert_sep)
                    assert prong2[0][0] == -abs(level) - 1
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

    horizontal_nodes : a list of length N, where the i-th entry consists of horizontal nodes (might be empty) in the form
    "[(label1, h1), (label2, h2)]"
    , where:
    - label1 and label2 are the indices of the veering triangulation in the list of veering triangulations
    - the half-edges h1 and h2 are contained in the boundary face of simple poles.

    prong_matching : a list consistings of pairs (prong1,prong2) with
    prong1 = ((level1, label1), h1, angle1)
    prong2 = ((level2, label2), h2, angle2)
    where:
    - level1 > level2
    - h1 is an half-edge at a zero of the veering triangulation 'vt1' at level1, and h2 is an hal-edge in a boundary face of the veering triangulation 'vt2' at level2
    - angle1 and angle2 are the indices of the vertical separatrices in the corner of h1 and h2 respectively satisfying that:
    the angle1 is in [0, vt1._num_vertical_separatrices_in_corner(h1)],
    and the angle2 is in [0, vt2._num_vertical_separatrices_in_corner(h2)].

    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from veerer.multiscale_veering_triangulation import *

    An example with non-trivial glabal residue condition::

        sage: vt = VeeringTriangulation("(0,1,2)(4,~2,3)(~3,5,6)(~6,~0,~1)(11, 12,~10)(8,9,10)(~13, 7, ~9)(13,~11,~12)(~5,~7,14)(~14,~4,~8)", "RBBBRRBBBRRBRRB")
        sage: vt.stratum()
        H_3(4)
        sage: vt.is_delaunay()
        True
        sage: edges_low = [4,5,7,8,14]
        sage: mvt = MultiscaleVeeringTriangulation([vt], [[]], [])
        sage: mvt1 = mvt.degeneration(0,0,edges_low=edges_low)
        sage: mvt1
        MultiscaleVeeringTriangulation(
        veering_triangulations=[
            VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)]),
            VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
        ],
        horizontal_nodes=[[], []],
        prong_matching=[[((0, 0), 0, 0), ((-1, 0), 0, 0)], [((0, 0), 10, 0), ((-1, 0), 4, 0)]]
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

    def __init__(self, veering_triangulations=None, horizontal_nodes=None, prong_matching=None, check=True):

        if isinstance(veering_triangulations, list):
            self._veering_triangulations = []
            NN = len(veering_triangulations)
            for level in range(NN):
                l = veering_triangulations[level]
                if isinstance(l, VeeringTriangulation):
                    self._veering_triangulations.append([l])
                elif isinstance(l, list):
                    for vt in l:
                        if not isinstance(vt, VeeringTriangulation):
                            raise ValueError(f"'vt' (value: {vt}) is not an instance of the VeeringTriangulation.")
                    self._veering_triangulations.append(list(l))
                else:
                    raise ValueError(f"The input {l} is bad.")
        else:
            raise ValueError("The 'veering_triangulations' must be a list.")

        if isinstance(horizontal_nodes, list):
            if len(horizontal_nodes) != len(self._veering_triangulations):
                raise ValueError("Miss information of horizontal nodes at some levels")
            self._horizontal_nodes = []
            for level in range(len(horizontal_nodes)):
                self._horizontal_nodes.append([])
                nodes = horizontal_nodes[level]

                for i in range(len(nodes)):

                    node = nodes[i]
                    p1, p2 = node
                    c1, h1 = p1
                    c2, h2 = p2

                    # normalization of horizontal nodes
                    if isinstance(p1[1], str):
                        h1 = str_to_label(p1[1])
                    if isinstance(p2[1], str):
                        h2 = str_to_label(p2[1])
                    f1, f2 = self.horizontal_faces(level, [(c1, h1), (c2, h2)])
                    nodes[i] = sorted([(c1, min(f1)), (c2, min(f2))], key=lambda x: (x[0], x[1]))

                for node in nodes:
                    if check:
                        self._check_horizontal_node(level, node)
                    self._horizontal_nodes[level].append(node)
                self._horizontal_nodes[level] = sorted(self._horizontal_nodes[level], key=lambda x: (x[0][0], x[1][0], x[0][1]))
        else:
            raise ValueError("The 'horizontal_nodes' must be a list.")

        if isinstance(prong_matching, list):
            self._prong_matching = []
            for pm in prong_matching:
                prong1, prong2 = pm

                if isinstance(prong1[1], str):
                    h = str_to_label(prong1[1])
                    prong1 = (prong1[0],h,prong1[2])
                if isinstance(prong2[1], str):
                    h = str_to_label(prong2[1])
                    prong2 = (prong2[0],h,prong2[2])

                pm = [prong1, prong2]
                if check:
                    self._check_local_prong_matching(pm)

                # adjust prong2 according to our convention that we do not consider the last prong in the each corner
                m2, h2, ang = prong2
                level2, c2 = m2
                vt = self._veering_triangulations[abs(level2)][c2]
                assert vt.face_angle(h2) != 0
                last_ang = _num_vertical_separatrices_in_corner(vt, h2) - 1 #the valid range is between 1 and the number of vertical separatrices
                while ang == last_ang:
                    h2 = vt.previous_in_face(h2)
                    ang = 0
                    prong2 = ((level2, c2), h2, ang)
                    last_ang = _num_vertical_separatrices_in_corner(vt, h2) - 1
                #Note that the resulting prong2 is always equivalent to the original prong2

                pm = [prong1, prong2]

                prongs1, prongs2 = self._local_prong_matching(pm)
                assert prongs1.index(prong1) == prongs2.index(prong2)

                # normalization of prong1
                filtered = [prong for prong in prongs1 if prong[2] == 0]
                prong1 = min(filtered, key=lambda x: x[0])
                prong2 = prongs2[prongs1.index(prong1)]

                self._prong_matching.append([prong1, prong2])
            self._prong_matching = sorted(self._prong_matching, key=lambda x: (-x[0][0][0], x[0][0][1], x[0][1]))
        else:
            raise ValueError("The 'prong_matching' must be a list.")

        if check:
            self._check_prong_matching()
            self._check_horizontal_residue_conditions()

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

    def _check_horizontal_node(self, level, node):

        level = self._check_level(level)

        p1, p2 = node
        c1, h1 = p1
        c2, h2 = p2
        vt1 = self._veering_triangulations[abs(level)][c1]
        vt2 = self._veering_triangulations[abs(level)][c2]

        if (vt1.face_angle(h1) != 0):
            raise ValueError(f"The half-edge {h1} is not in the face of simple pole")
        elif (vt2.face_angle(h2) != 0):
            raise ValueError(f"The half-edge {h2} is not in the face of simple pole")

        f0, f1 = self.horizontal_faces(level, node)
        if (f0 == f1) and (c1 == c2):
            raise ValueError(f"The half-edge {h1} and {h2} cannot be in the same face")
        for hh in f0:
            for hhh in f1:
                if vt1._colouring[hh // 2] != vt2._colouring[hhh // 2]:
                    raise ValueError(f"The boundary edges in two faces of {h1} and {h2} have different colors")
    
    def _check_horizontal_residue_conditions(self):
        N = self.num_levels()
        horiz_nodes = self._horizontal_nodes
        for level in range(N):
            nodes = horiz_nodes[level]

            for node in nodes:
                p1, p2 = node
                c = p1[0]
                assert c == p2[0]

                vt = self._veering_triangulations[level][c]
                base_ring = vt.base_ring()
                orig_constraints_matrix = vt.constraints_matrix()
                n1 = orig_constraints_matrix.nrows()
                constraints_matrix = matrix(base_ring, n1 + 1, vt.num_edges())
                constraints_matrix[:n1, :] = orig_constraints_matrix

                #build the ``residue`` matrix for simple poles
                bdry = vt.boundary_faces()
                nf = len(bdry)
                ne = vt._ne
                r = matrix(ZZ, nf, ne)
                for i, f in enumerate(bdry):
                    if vt.face_angle(f[0]) == 0:
                        for h in f:
                            r[i, h // 2] = 1 #if f has face angle zero, the colors on the boundary must be the same

                #build reisdue conditions:
                f1, f2 = self.horizontal_faces(level, node)
                rr = matrix(ZZ, 1, nf)
                rr[0, bdry.index(f1)] = 1
                rr[0, bdry.index(f2)] = -1
                constraints_matrix[n1:, :] = rr * r
                gens = constraints_matrix.right_kernel_matrix()
                from .linear_family import VeeringTriangulationLinearFamily
                vt_test = VeeringTriangulationLinearFamily(vt, gens)

                if not (vt_test == vt.as_linear_family()):
                    raise ValueError(f"The horizontal node {node} at level {-level} do not satisfy the residue condition")

    def _check_local_prong_matching(self, pm):
        r"""
        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: from veerer.multiscale_veering_triangulation import *
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: pm = [((0, 0), 0,4),((-1, 0), 0, 1)]
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: The angle label of ((0, 0), 0, 4) is out of the valid range [0, 3].
            sage: pm = [((0, 0),7,0),((-1, 0),0,1)]
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: The corner of ((0, 0), 7, 0) is not a red-blue corner
            sage: pm = [((0,0),1,0),((-1,0),0,1)]
            sage: MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[pm])
            Traceback (most recent call last):
            ...
            ValueError: The orders of the zero in ((0, 0), 1, 0) and  the pole in ((-1, 0), 0, 1) are not matched
        """

        NN = len(self._veering_triangulations)
        prong1, prong2= pm

        m1, h1, a1 = prong1
        m2, h2, a2 = prong2
        l1, c1 = m1
        l2, c2 = m2

        #check the levels are valid
        if (l1 > 0) or (l2 > 0) or (-l1 >= NN) or (-l2 >= NN):
            raise ValueError(f"The levels in {pm} are invalid")
        if (l1 <= l2):
            raise ValueError(f"The level of {prong1} should be greater than the level of {prong2}")

        vt1 = self._veering_triangulations[abs(l1)][c1]
        vt2 = self._veering_triangulations[abs(l2)][c2]

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
            num_v = _num_vertical_separatrices_in_corner(vt1,h1)
            if a1 not in range(num_v):
                raise ValueError(f"The angle label of {prong1} is out of the valid range [0, {num_v - 1}].")

        #check prong2
        if alpha2[h2] == 0:
            raise ValueError(f"The input {prong2} is not in boundary")
        else:
            num_p = _num_vertical_separatrices_in_corner(vt2,h2)
            if a2 not in range(num_p):
                raise ValueError(f"The angle label of {prong2} is out of the valid range [0, {num_p}].")

    def _check_prong_matching(self):
        pms = self._prong_matching
        NN = self.num_levels()
        for level in range(NN):
            l1 = []
            l2 = []
            for pm in pms:
                p1, p2 = pm
                if p1[0][0] == level:
                    v = self.vertical_node(pm)[0]
                    if v in l1:
                        raise ValueError(f"There are prongs at the same zero as {pm[0]}")
                    else:
                        l1.append((p1[0][1], v))
                if p2[0][0] == level:
                    f = self.vertical_node(pm)[1]
                    if f in l2:
                        raise ValueError(f"There are prongs at the same pole as {pm[1]}")
                    else:
                        l2.append((p2[0][1], f))

    def __str__(self):
        vt_strings = ",\n    ".join(", ".join(str(vt) for vt in l) for l in self._veering_triangulations)
        horizontal_nodes_str = "[" + ", ".join(str(hn) for hn in self._horizontal_nodes) + "]"
        prong_matching_str = "[" + ", ".join(str(pm) for pm in self._prong_matching) + "]"
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
        return (self._veering_triangulations == other._veering_triangulations) and (self._horizontal_nodes == other._horizontal_nodes) and (self._prong_matching == other._prong_matching)

    def __ne__(self, other):
        if type(self) != type(other):
            raise TypeError
        return self._veering_triangulations != other._veering_triangulations and self._horizontal_nodes != other._horizontal_nodes and self._prong_matching != other._prong_matching

    def __hash__(self):
        veering_triangulations_hashable = tuple(
            tuple(map(hash, level)) for level in self._veering_triangulations
        )
        horizontal_nodes_hashable = tuple(
            tuple(tuple(node) for node in level) for level in self._horizontal_nodes
        )
        prong_matching_hashable = tuple(
            tuple(tuple(prong) for prong in match) for match in self._prong_matching
        )
        return hash((veering_triangulations_hashable, horizontal_nodes_hashable, prong_matching_hashable))

    def veering_triangulation_at_level(self, level):
        level = self._check_level(level)
        return self._veering_triangulations[level]

    def num_levels(self):
        return len(self._veering_triangulations)

    def horizontal_faces(self, level, node):
        r"""
        Return a pair of faces corresponding to the node
        """
        level = self._check_level(level)
        p1, p2 = node

        vt1 = self._veering_triangulations[level][p1[0]]
        vt2 = self._veering_triangulations[level][p2[0]]

        f0 = None
        f1 = None
        for f in vt1.boundary_faces():
            if p1[1] in f:
                f0 = f

        for f in vt2.boundary_faces():
            if p2[1] in f:
                f1 = f

        if f0 is None or f1 is None:
            raise ValueError(f"The horizontal node {node} at level {level} is not between boundary faces")
        return (f0, f1)

    def horizontal_nodes_at_level(self, i):
        r"""
        Return the list of horizontal nodes at the level of the input 'i'.

        Each node is represented by a triple (level,label0,face0,label1,face1).

        EXAMPLES::
        """
        i = self._check_level(i)

        l = self._horizontal_nodes[abs(i)]
        list_horiz_nodes = []
        if len(l) != 0:
            for node in l:
                f0, f1 = self.horizontal_faces(i, node)
                list_horiz_nodes.append((-i, node[0][0],f0, node[1][0],f1))

        return list_horiz_nodes

    def vertical_node(self, pm):
        r"""
        Return the underlying node of the prong matching.

        The vertical node is represented as a pair of zero and face
        """
        p1, p2 = pm
        m1, h1, _ = p1
        m2, h2, _ = p2
        vt1 = self._veering_triangulations[abs(m1[0])][m1[1]]
        vt2 = self._veering_triangulations[abs(m2[0])][m2[1]]
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

            sage: from veerer import VeeringTriangulation
            sage: from veerer.multiscale_veering_triangulation import *
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[((0,0),"0",0),((-1,0),"0",1)],[((0,0),"2",0),((-1,0),"5",1)]])
            sage: mvt0._local_prong_matching([((0,0),0,0),((-1,0),0,1)])
            [[((0, 0), 0, 0), ((0, 0), 0, 1), ((0, 0), 0, 2), ((0, 0), 0, 3)],
            [((-1, 0), 0, 1), ((-1, 0), 0, 2), ((-1, 0), 0, 3), ((-1, 0), 0, 0)]]
        """

        p1, p2 = pm
        m1, h1, _ = p1
        m2, h2, _ = p2
        l1, c1 = m1
        l2, c2 = m2

        vt1 = self._veering_triangulations[abs(l1)][c1]
        vt2 = self._veering_triangulations[abs(l2)][c2]
        alpha1 = vt1.boundary_vector()

        for v in vt1.vertices():
            if h1 in v:
                zero = v
        for f in vt2.boundary_faces():
            if h2 in f:
                pole = f

        vp1 = vt1.vertex_permutation()

        prongs1 = [] #list of prongs at the zero
        prongs2 = [] #list of prongs at the pole

        # compute the list of prongs at the zero.
        for h in zero:
            if alpha1[h] == 0: #internal edge
                hh = vp1[h]
                if (vt1._colouring[h // 2] == RED) and (vt1._colouring[hh // 2] == BLUE): #h corresponds to a red-blue corner
                    prongs1.append((m1,h,0))
            else:
                num_p = _num_vertical_separatrices_in_corner(vt1, h)
                for j in range(num_p):
                    prongs1.append((m1,h,j))

        #compute the list of prongs at the pole
        pole.reverse()
        for h in pole:
            num_p = _num_vertical_separatrices_in_corner(vt2, h) - 1
            for j in range(num_p):
                    prongs2.append((m2,h,j))

        assert len(prongs1) == len(prongs2)

        # match the prongs. Shift the lists so that the corresponding indices are matched.
        index1 = prongs1.index(p1)
        shiftprong1 = prongs1[index1:] + prongs1[:index1]

        index2 = prongs2.index(p2)
        shiftprong2 = prongs2[index2:] + prongs2[:index2]

        return [shiftprong1, shiftprong2]

    def prong_matching_map(self, prong):
        r"""
        Return the prong matched with the input prong.

        The prong is represented in the form of (level, half-edge, angle label)
        """
        for pm in self._prong_matching:
            prongs1, prongs2 = self._local_prong_matching(pm)
            if prong in prongs1:
                j = prongs1.index(prong)
                return prongs2[j]
            if prong in prongs2:
                j = prongs2.index(prong)
                return prongs1[j]

    def _components_have_horiztal_nodes_with(self, level, label, comp_index):
        r"""
        Return the indices of the components that have horizontal nodes with the input component.
        """
        l_node = self.horizontal_nodes_at_level(level)

        l = []
        for level, s1, f1, s2, f2 in l_node:
            #compute the component indices of the face f1 and f2
            vt1 = self._veering_triangulations[abs(level)][s1]
            vt2 = self._veering_triangulations[abs(level)][s2]
            c1 = in_connected_component(vt1, f1[0])
            c2 = in_connected_component(vt2, f2[0])

            if (s1, c1) == (label, comp_index):
                l.append((level, s2, c2))
            if (s2, c2) == (label, comp_index):
                if (level,s1,c1) not in l:
                    l.append((level,s1,c1))
        return l

    def is_abelian(self, certificate=False):
        r"""
        Return whether the multi-scale veering triangulation is Abelian.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.multiscale_veering_triangulation import *

        A horizontal node between the same components::

            sage: vt = VeeringTriangulationLinearFamily("(0,1,4)(2,3,~4)(~0:1)(~1:1)(~2:1)(~3:1)", "RBBRR", [(1, 0, 0, 1, 1), (0, 1, 1, -2, -1)])
            sage: mvt = MultiscaleVeeringTriangulation([vt],[[[(0,"~1"),(0,"~2")]]],[])
            sage: mvt.is_abelian()
            False

        Mix of horizontal and vertical nodes::
            sage: vt0 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
            sage: vt1 = VeeringTriangulationLinearFamily("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(2:1)(~3:1)(~4:1)(5:5)(7:1)(~8:1)(~9:1)", "BBRBRBBRBR", [(1, 0, 0, 0, 1, 0, 0, 1, 1, 0), (0, 1, 0, 1, -1, 0, 0, -1, -1, 0), (0, 0, 1, 1, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 1, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, 1, 0, 1, -1)])
            sage: vt0.is_abelian()
            True
            sage: vt1.is_abelian()
            True
            sage: mvt0 = MultiscaleVeeringTriangulation([vt0,vt1],[[],[[(0,"~4"),(0,"7")]]],[[((0,0),"0",0),((-1,0),"0",1)],[((0,0),"2",0),((-1,0),"5",1)]])
            sage: mvt0.is_abelian()
            False
            sage: vt2 = VeeringTriangulationLinearFamily("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(2:1)(~3:1)(~4:1)(5:5)(7:1)(~8:1)(~9:1)", "BBRBRBBRBR", [(1, 0, 0, 0, 1, 0, 0, 0, 0, 0), (0, 1, 0, 1, -1, 0, 0, 1, 1, 0), (0, 0, 1, 1, 0, 0, 0, 1, 1, 0), (0, 0, 0, 0, 0, 1, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, 1, -1, 0, -1)])
            sage: mvt1 = MultiscaleVeeringTriangulation([vt0,vt2],[[],[[(0,"~3"),(0,"~8")]]],[[((0,0),"0",0),((-1,0),"0",1)],[((0,0),"2",0),((-1,0),"5",1)]])
            sage: print(mvt1.is_abelian(certificate=True))
            (True, [[[True, False, True, False, False, True, False, True, False, True]], [[False, True, False, True, False, True, False, True, False, True, True, False, True, False, True, False, True, False, True, False]]])
        """

        NN = self.num_levels()
        oris = [[] for _ in range(NN)]

        #Step1: propagate level-wise
        for i in range(NN):
            vts = self._veering_triangulations[i]
            for vt in vts:
                abelian, l = vt.is_abelian(certificate=True)
                if abelian:
                    oris[i].append(l)
                else:
                    return (False, None) if certificate else False

        #Step2: propagate through horizontal nodes
        for i in range(NN):
            #vt = self.veering_triangulation_at_level(-i)
            vts = self._veering_triangulations[i]
            l_component = []
            for vt in vts:
                l_component.append(vt.connected_components())

            l_nodes = self.horizontal_nodes_at_level(-i)
            lc = [] #the list of components in the level-(-i) adjusted so far
            for level, s1, f1, s2, f2 in l_nodes:
                # find out the components containing the matched poles
                vt1 = self._veering_triangulations[abs(level)][s1]
                vt2 = self._veering_triangulations[abs(level)][s2]

                c1 = in_connected_component(vt1, f1[0])
                c2 = in_connected_component(vt2, f2[0])

                lo1 = oris[i][s1]
                lo2 = oris[i][s2]
                ne1 = len(lo1)
                ne2 = len(lo2)

                if lo1[f1[0]] == lo2[f2[0]]:
                    #check the coherence
                    if c1 == c2:
                        return (False, None) if certificate else False

                    if ((s1,c1) in lc) and ((s2,c2) in lc):
                        return (False, None) if certificate else False

                    if (s1,c1) not in lc:
                        #rotate the component c1 by pi
                        for h in range(ne1):
                            if h // 2 in l_component[s1][c1]:
                                lo1[h] = not lo1[h]
                        #add coherent components
                        lc.append((s1,c1))
                        if (s2, c2) not in lc:
                            lc.append((s2,c2))
                    elif (s2,c2) not in lc:
                        #rotate the component c2 by pi
                        for h in range(ne2):
                            if h // 2 in l_component[s2][c2]:
                                lo2[h] = not lo2[h]
                        lc.append((s2,c2))
                else:
                    #add coherent components
                    if (s1,c1) not in lc:
                        lc.append((s1,c1))
                    if (s2,c2) not in lc:
                        lc.append((s2,c2))

                oris[i][s1] = lo1
                oris[i][s2] = lo2

        #Step3: propagate through vertical nodes

        lv = [] #the list of component adjusted so far, where the component is labeled by (level, index of the component in this level)

        for pm in self._prong_matching:

            m1, h1, ang1 = pm[0]
            m2, h2, ang2 = pm[1]
            level1, s1 = m1
            level2, s2 = m2

            vt1 = self._veering_triangulations[abs(level1)][s1]
            vt2 = self._veering_triangulations[abs(level2)][s2]

            o1 = oris[-level1][s1][h1]
            o2 = oris[-level2][s2][h2]

            #decide the orientation of the prong pm[0]
            if (ang1)%2 == 1:
                o1 = not o1

            #decide the orientation of the prong pm[1]
            if (ang2)%2 == 1:
                o2 = not o2

            #find the labels of the components where the prongs are.
            #the labels are in the form: (level, index of the component in this level)
            #moreover find out all the components that have horizontal nodes with the components containing the prongs
            c1 = in_connected_component(vt1, h1)
            l1 = self._components_have_horiztal_nodes_with(level1, s1, c1)
            if (level1, s1, c1) not in l1:
                l1.append((level1, s1, c1))

            c2 = in_connected_component(vt2, h2)
            l2 = self._components_have_horiztal_nodes_with(level2,s2, c2)
            if (level2, s2, c2) not in l2:
                l2.append((level2, s2, c2))

            #adjust the components
            lo1 = oris[-level1][s1]
            n1 = len(lo1)
            lo2 = oris[-level2][s2]
            n2 = len(lo2)
            if o1 != o2:#incoherent
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
            else: #coherent orientation
                if (level1, s1, c1) not in lv:
                    for label in l1:
                        lv.append(label)
                if (level2, s2, c2) not in lv:
                    for label in l2:
                        lv.append(label)

            oris[-level1][s1] = lo1
            oris[-level2][s2] = lo2

        return (True, oris) if certificate else True

    def degeneration(self, level, component, edges_low=None, edges_up=None):
        r"""
        Return the multi-scale veering triangulation by blowing-up the given subset of ``edge``.

        This corresponds to an either a horizontal degeneration or a vertical degeneration in the BCGGM compactification.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.multiscale_veering_triangulation import *

        Reach all vertical boundary component of H_1(2) from a single veering triangulaiton (TO BE COMPLETED)::

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BRBBRBBRB")
            sage: vt.stratum()  # optional - surface_dynamics
            H_2(2)
            sage: mvt = MultiscaleVeeringTriangulation([vt],[[]],[])
            sage: vt.vertical_degeneration_low_edges_subsets()
            [(1,), (4,), (7,), (4, 7), (1, 4)]
            sage: mvt1 = mvt.degeneration(0,0, edges_low=(1,))
            sage: mvt2 = mvt.degeneration(0,0, edges_low=(4,))
            sage: mvt3 = mvt1.degeneration(0,0, edges_low=(4,))

        More examples::

            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[((0,0),"0",0),((-1,0),"0",1)],[((0,0),"2",0),((-1,0),"5",1)]])
            sage: mvt0.degeneration(-1,0, edges_low=[0, 1, 2, 3, 4, 5], edges_up=[6, 7])
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)", "RBRBB"),
                VeeringTriangulationLinearFamily("(~0,1,2)(~1,~2,3)(0:5)(~3:1)(4:4,5:4)(~4:1)(~5:1)", "BBRBBB", [(1, 0, 1, 1, 0, 0), (0, 1, -1, 0, 0, 0), (0, 0, 0, 0, 1, 1)])
            ],
            horizontal_nodes=[[], [[(0, 9), (0, 11)]]],
            prong_matching=[[((0, 0), 0, 0), ((-1, 0), 0, 1)], [((0, 0), 4, 0), ((-1, 0), 10, 1)]]
            )
        """

        vts = copy.deepcopy(self._veering_triangulations)
        vt = vts[abs(level)][component]
        nh = 2 * (vt.num_edges())
        ep = vt.edge_permutation()

        f_up ,f_low, r_up, r_low = vt.degeneration(edges_low=edges_low, edges_up=edges_up, collapsed_half_edge_relabelling=True)

        #build list of veering triangulations.
        #TO BE CONFIRMED: there are choices of the component in the original level ``level`` in the new levels. However, since we will consider all possible vertical degenerations, we could consider just one case that their levels remain the same.

        if f_up is None:
            vts[abs(level)][component] = f_low
        else:
            vts[abs(level)][component] = f_up
            vts.insert(abs(level) + 1, [f_low])

        #build the horizontal nodes
        l1 = []
        l2 = []
        l_horiz = copy.deepcopy(self._horizontal_nodes)
        #existing horizontal nodes
        for a1, a2 in self._horizontal_nodes[abs(level)]:
            c1, h1 = a1
            c2, h2 = a2
            if r_up[h1] >= 0:
                h1 = r_up[h1]
                h2 = r_up[h2]
                assert h2 >= 0
                l1.append([(c1, h1),(c2, h2)])
            else:
                h1 = r_low[h1]
                h2 = r_low[h2]
                assert h1 >= 0
                assert h2 >= 0
                if f_up is None:
                    l1.append([(c1, h1),(c2, h2)])
                else:
                    l2.append([(0,h1), (0, h2)])
        #new horizontal nodes
        if f_up is None:
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
                    node = sorted([(component, b1), (component, b2)], key=lambda x: (x[1]))
                    if node not in l1:
                        l1.append(node)
            l_horiz[abs(level)] = l1
        else:
            l_horiz.insert(abs(level) + 1, [])
            l_horiz[abs(level)] = l1
            l_horiz[abs(level) + 1] = l2

        #build the vertical nodes
        l_pm = []
        #existing vertical nodes
        original_pm = copy.deepcopy(self._prong_matching)
        for pm in original_pm:
            prong1, prong2 = pm
            if prong1[0] == (-abs(level), component):
                prong1 = track_prong(vt, r_up, r_low, prong1)
                if f_up is None:
                    l_pm.append([prong1,prong2])
                else:
                    prong2 = ((prong2[0][0] - 1,prong2[0][1]), prong2[1], prong2[2])
                    l_pm.append([prong1,prong2])
            elif prong2[0] == (-abs(level), component):
                prong2 = track_prong(vt, r_up, r_low, prong2)
                l_pm.append([prong1,prong2])
            else:
                l_pm.append(pm)
        #new vertical nodes
        if f_up is not None:
            l_pm  = l_pm + _new_prong_matching(vt, f_low, r_up, r_low, -abs(level), component)

        #build the degeneration
        return MultiscaleVeeringTriangulation(vts,l_horiz,l_pm)

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
            sage: from veerer.multiscale_veering_triangulation import *

            sage: vt = VeeringTriangulation("(~0,2,3)(~1,4,5)(~2,6,7)(~3,~5,8)(~4,9,10)(~6,11,12)(~7,13,14)(~8,~12,15)(~9,16,~15)(~11,17,18)(~14,~18,19)(~16,~17,20)(0:1)(1:1)(~10:1)(~13:1)(~19:1)(~20:1)", "BBRRRBBBRBBRRBRBRRBBB")
            sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[vt], horizontal_nodes=[[[(0, 0), (0, 2)], [(0, 21), (0, 27)], [(0, 39), (0, 41)]]], prong_matching=[])
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
            sage: from veerer.multiscale_veering_triangulation import *

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "RRBBRRRRBBBR")
            sage: edges_up = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
            sage: mvt0 = MultiscaleVeeringTriangulation([vt], [[]],[])
            sage: mvt = mvt0.degeneration(0,0,edges_up=edges_up)
            sage: mvt
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRRRRB", [(1, 0, -1, -1, 0, -1, -1, 0, 1), (0, 1, 1, 1, 0, 1, 1, 0, -1), (0, 0, 0, 0, 1, 1, 1, 0, -1), (0, 0, 0, 0, 0, 0, 0, 1, 1)]),
                VeeringTriangulationLinearFamily("(0:4,~0:4)", "R", [(1)])
            ],
            horizontal_nodes=[[], []],
            prong_matching=[[((0, 0), 11, 0), ((-1, 0), 0, 0)]]
            )
            sage: vt0 = mvt._veering_triangulations[0][0]
            sage: ds_graph = vt0.delaunay_strebel_graph()
            sage: path = LabelledDiGraphPath(ds_graph, 0, [3, 13, 16])
            sage: mvt.transport_along_path(0, 0, path)
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BRBBRRRBR", [(1, 0, 1, 1, 0, 1, 1, 0, 1), (0, 1, 1, 1, 0, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 0, 0, 0, 1, -1)]),
                VeeringTriangulationLinearFamily("(0:4,~0:4)", "R", [(1)])
            ],
            horizontal_nodes=[[], []],
            prong_matching=[[((0, 0), 16, 0), ((-1, 0), 0, 0)]]
            )
        """
        st_graph = path._graph
        vt0 = st_graph.vertex_label(path.start())
        vt1 = st_graph.vertex_label(path.end())
        assert self._veering_triangulations[abs(level)][component] == vt0

        vts = copy.deepcopy(self._veering_triangulations)
        vts[abs(level)][component] = vt1

        mono = SeparatrixMonodromy(st_graph)

        #new horizontal nodes
        l1 = []
        l_horiz = copy.deepcopy(self._horizontal_nodes)
        for node in l_horiz[abs(level)]:
            p1, p2 = node
            c1, h1 = p1
            c2, h2 = p2
            if c1 == component:
                h1 = mono.infinite_cylinder_transport(path, h1)
            if c2 == component:
                h2 = mono.infinite_cylinder_transport(path, h2)
            l1.append([(c1,h1),(c2,h2)])
        l_horiz[abs(level)] = l1

        #new vertical nodes
        l2 = []
        l_vert = copy.deepcopy(self._prong_matching)
        for pm in l_vert:
            p1, p2 = pm
            m1, h1, ang1 = p1
            m2, h2, ang2 = p2
            if m1 == (-abs(level), component):
                h1, ang1 = mono.vertex_separatrix_transport(path, h1, ang1)
            if m2 == (-abs(level), component):
                h2, ang2 = mono.face_separatrix_transport(path, h2, ang2)
            l2.append([(m1, h1, ang1),(m2, h2, ang2)])
        l_vert = l2

        return MultiscaleVeeringTriangulation(vts,l_horiz,l_vert)

    def prime_decomposition(self, level, component):
        r"""
        Return a prime decomposition of a component at ``(level, component)`` of multi-scale veering triangulation.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.multiscale_veering_triangulation import *

            sage: vt = VeeringTriangulation("(0,1,2)(4,~2,3)(~3,5,6)(~6,~0,~1)(11, 12,~10)(8,9,10)(~13, 7, ~9)(13,~11,~12)(~5,~7,14)(~14,~4,~8)", "RBBBRRBBBRRBRRB")
            sage: edges_low = [4,5,7,8,14]
            sage: mvt = MultiscaleVeeringTriangulation([vt], [[]], [])
            sage: mvt1 = mvt.degeneration(0,0,edges_low=edges_low)
            sage: mvt1
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)(3,4,5)(~3,~4,~5)", "RBBRBR", [(1, 0, -1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1), (0, 0, 0, 0, 1, -1)]),
                VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
            ],
            horizontal_nodes=[[], []],
            prong_matching=[[((0, 0), 0, 0), ((-1, 0), 0, 0)], [((0, 0), 10, 0), ((-1, 0), 4, 0)]]
            )
            sage: mvt1.prime_decomposition(0, 0)
            MultiscaleVeeringTriangulation(
              veering_triangulations=[
                VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RBB", [(1, 0, -1), (0, 1, 1)]), VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)]),
                VeeringTriangulationLinearFamily("(~0,~3,~4)(~1,~2,4)(0:2,1:2)(2:2,3:2)", "RRBBB", [(1, 1, 0, 0, -1), (0, 0, 1, 1, 1)])
              ],
              horizontal_nodes=[[], []],
              prong_matching=[[((0, 0), 0, 0), ((-1, 0), 0, 0)], [((0, 1), 0, 0), ((-1, 0), 4, 0)]]
            )
        """
        vts = copy.deepcopy(self._veering_triangulations)
        vt = vts[abs(level)][component]

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
        vts[abs(level)][component : component + 1] = l_vts_canonical

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
        l1 = []
        l_horiz = copy.deepcopy(self._horizontal_nodes)
        for node in l_horiz[abs(level)]:
            p1, p2 = node
            c1, h1 = p1
            c2, h2 = p2
            if c1 == component:
                cp1, h1 = label_in_prime_comp(h1, l_comp, l_mapping)
                p1 = (cp1 + component, h1)
            if c2 == component:
                cp2, h2 = label_in_prime_comp(h2, l_comp, l_mapping)
                p2 = (cp2 + component, h2)
            if c1 > component:
                p1 = (c1 + len(l_vts_canonical) - 1, h1)
            if c2 > component:
                p2 = (c2 + len(l_vts_canonical) - 1, h2)
            l1.append([p1,p2])
        l_horiz[abs(level)] = l1

        #new vertical nodes
        l2 = []
        l_vert = copy.deepcopy(self._prong_matching)
        for pm in l_vert:
            p1, p2 = pm
            m1, h1, ang1 = p1
            m2, h2, ang2 = p2
            if m1 == (-abs(level), component):
                cp1, h1 = label_in_prime_comp(h1, l_comp, l_mapping)
                p1 = ((-abs(level), cp1 + component), h1, ang1)
            if m2 == (-abs(level), component):
                cp2, h2 = label_in_prime_comp(h2, l_comp, l_mapping)
                p2 = ((-abs(level), cp2 + component), h2, ang2)
            if m1[0] == -abs(level) and m1[1] > component:
                p1 = ((-abs(level), m1[1] + len(l_vts_canonical) - 1), h1, ang1)
            if m2[0] == -abs(level) and m2[1] > component:
                p2 = ((-abs(level), m2[1] + len(l_vts_canonical) - 1), h2, ang2)
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

        from itertools import product
        l_g = []
        l_info = []
        for dsg in ld:
            i = ld.index(dsg)
            level, c = lc[i]
            vt = self._veering_triangulations[abs(level)][c]

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

            monog0 = monodromy(dsg)
            monog = [perm_init(f"{p}", n=n) for p in monog0]
            l_g.append(monog)

        from itertools import product
        G = product(*l_g)
        lmvts = set()
        for g in G:
            #do not change veering triangulations
            vts = copy.deepcopy(self._veering_triangulations)

            #new horizontal nodes
            l_horiz = copy.deepcopy(self._horizontal_nodes)
            for level in range(len(self._veering_triangulations)):
                l1 = []
                for node in l_horiz[abs(level)]:
                    p1, p2 = node
                    c1, h1 = p1
                    c2, h2 = p2
                    if (-abs(level), c1) in lc: #if the face is contained in the component in the lc
                        i = lc.index((-abs(level), c1))
                        vertex_separatrices, vertex_separatrix_index, face_separatrices, face_separatrix_index, infinite_cylinders, infinite_cylinder_index, nv, nf, nc, n = l_info[i]

                        a = infinite_cylinder_index[h1]
                        aa = g[i][a]
                        h1 = infinite_cylinders[aa - nv - nf]
                    if (-abs(level), c2) in lc:
                        i = lc.index((-abs(level), c2))
                        vertex_separatrices, vertex_separatrix_index, face_separatrices, face_separatrix_index, infinite_cylinders, infinite_cylinder_index, nv, nf, nc, n = l_info[i]

                        a = infinite_cylinder_index[h2]
                        aa = g[i][a]
                        h2 = infinite_cylinders[aa - nv - nf]
                    l1.append([(c1,h1),(c2,h2)])
                l_horiz[abs(level)] = l1

            #new vertical nodes
            l2 = []
            l_vert = copy.deepcopy(self._prong_matching)
            for pm in l_vert:
                p1, p2 = pm
                m1, h1, ang1 = p1
                m2, h2, ang2 = p2

                if m1 in lc:#the zero of the node is contained in the component
                    i = lc.index(m1)
                    vertex_separatrices, vertex_separatrix_index, face_separatrices, face_separatrix_index, infinite_cylinders, infinite_cylinder_index, nv, nf, nc, n = l_info[i]

                    a = vertex_separatrix_index[(h1, ang1)]
                    aa = g[i][a]
                    h1, ang1 = vertex_separatrices[aa]
                if m2 in lc: #the pole of the node is contained in the component
                    i = lc.index(m2)
                    vertex_separatrices, vertex_separatrix_index, face_separatrices, face_separatrix_index, infinite_cylinders, infinite_cylinder_index, nv, nf, nc, n = l_info[i]

                    a = face_separatrix_index[(h2, ang2)]
                    aa = g[i][a]
                    h2, ang2 = face_separatrices[aa - nv]
                l2.append([(m1, h1, ang1),(m2, h2, ang2)])
            l_vert = l2

            mvtnew = MultiscaleVeeringTriangulation(vts,l_horiz,l_vert)
            lmvts.add(mvtnew)
        return list(lmvts)

    def transport_by_permutation_in_levels(self):
        r"""
        Return the list of multi-scale veering triangulations by permutes the same components in each level.
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
                g = p[i] #permutation at level-i
                level_horiz = orig_horiz_nodes[i]
                new = []
                for p1, p2 in level_horiz:
                    c1, h1 = p1
                    c2, h2 = p2
                    c1 = g[c1]
                    c2 = g[c2]
                    new.append([(c1, h1), (c2, h2)])
                new_horiz_nodes[i] = new

            #new prong-matchings
            orig_pms = copy.deepcopy(self._prong_matching)
            new_pms = []
            for p1, p2 in orig_pms:
                m1, h1, ang1 = p1
                m2, h2, ang2 = p2
                l1, c1 = m1
                l2, c2 = m2
                m1 = (l1, p[l1][c1])
                m2 = (l2, p[l2][c2])
                new_pms.append([(m1, h1, ang1), (m2, h2, ang2)])

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
            sage: from veerer.multiscale_veering_triangulation import *

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "RRBBRRRRBBRR")
            sage: mvt = MultiscaleVeeringTriangulation([vt], [[]], [])
            sage: D = PrimeDegenerations()
            sage: ds_graph = vt.delaunay_strebel_graph()
            sage: l1 = D.codimension_one_vertical_degenerations(ds_graph)
            sage: D.find(ds_graph)
            0
            sage: lmvt1 = mvt.codimension_one_vertical_prime_degenerations(0, 0, 0, D)
            sage: mvt1 = lmvt1[0][0]
            sage: vt0 = mvt1._veering_triangulations[0][0]
            sage: ds_graph0 = vt0.delaunay_strebel_graph()
            sage: l2 = D.codimension_one_vertical_degenerations(ds_graph0)
            sage: D.find(ds_graph0)
            2
            sage: lmvt2 = mvt1.codimension_one_vertical_prime_degenerations(0, 0, 2, D)
            sage: mvt2 = lmvt2[0][0]
            sage: mvt2._veering_triangulations
            [[VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])],
            [VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)])],
            [VeeringTriangulationLinearFamily("(0:4,~0:4)", "R", [(1)])]]
            sage: l2[0]
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

        vt = self._veering_triangulations[abs(level)][component]
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
            lc0 = [(-abs(level), component + index) for index in range(len(list_comp_up))]
            lc1 = [(-abs(level) - 1, index) for index in range(len(list_comp_low))]
            lc = lc0 + lc1
            ld = l_ds_g_up + l_ds_g_low

            #construct paths
            target_vertices = [ds_graph.vertex_index(a[0]) for a in l_vt_edge]
            paths = tree_with_target(ds_graph, root=0, target_vertices=target_vertices)
            assert len(paths) == len(l_vt_edge)

            #transport mvt
            lmvt = [self.transport_along_path(-abs(level), component, path) for path in paths]
            assert len(lmvt) == len(l_vt_edge)

            #make vertical degeneration and compute all transitions under monodromy groups and level-wise permutations
            l_deg_connected_comps = []
            all_mvt = []
            for i, mvt in enumerate(lmvt):
                _, edges_up, edges_low = l_vt_edge[i]
                mvt = mvt.degeneration(-abs(level), component, edges_low=edges_low, edges_up=edges_up)
                mvt = mvt.prime_decomposition(-abs(level), component)
                mvt = mvt.prime_decomposition(-abs(level) - 1, 0)

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
        Return a list of lists of lists of multi-scale veering triangulations obtained 
        by codimension-one horizontal degenerations of the component.

        The returned list is organized as `l = [[l00, l01, ...], [l10, l11, ...], ...]`, where:
        - Each sublist `[li0, li1, ...]` contains multi-scale veering triangulations with the same enhanced level graph.
        The corresponding components of these triangulations belong to the same cell of veering triangulations.
        These sublists align with the `i`-th object in `D.codimension_one_horizontal_degenerations(ds_graph)`.

        - Each `lij` within the sublists consists of multi-scale veering triangulations that are in the same 
        connected component of the linear subvariety.

        Input:
        - `ds_graph`: The Delaunay-Strebel graph of the prime component (which is the `component`-th component at the `level`).
        - `D`: An instance of the `PrimeDegeneration` class, responsible for computing the codimension-one horizontal degenerations 
        of the `component` in `ds_graph`.

        EXAMPLES::
            sage: from veerer import *
            sage: from veerer.linear_subvariety import *
            sage: from veerer.labelled_digraph import *
            sage: from veerer.monodromy import *
            sage: from veerer.multiscale_veering_triangulation import *

            sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "RRBBRRRRBBRR")
            sage: mvt = MultiscaleVeeringTriangulation([vt], [[]], [])
            sage: D = PrimeDegenerations()
            sage: ds_graph = vt.delaunay_strebel_graph()
            sage: l1 = D.codimension_one_vertical_degenerations(ds_graph)
            sage: D.find(ds_graph)
            0
            sage: mvt1 = mvt.codimension_one_vertical_prime_degenerations(0, 0, 0, D)[0][0]
            sage: vt0 = mvt1._veering_triangulations[0][0]
            sage: ds_graph0 = vt0.delaunay_strebel_graph()
            sage: l2 = D.codimension_one_vertical_degenerations(ds_graph0)
            sage: D.find(ds_graph0)
            2
            sage: mvt2 = mvt1.codimension_one_vertical_prime_degenerations(0, 0, 2, D)[0][0]
            sage: vt1 = mvt2._veering_triangulations[1][0]
            sage: ds_graph1 = vt1.delaunay_strebel_graph()
            sage: l3 = D.codimension_one_horizontal_degenerations(ds_graph1)
            sage: D.find(ds_graph1)
            8
            sage: lmvts = mvt2.codimension_one_horizontal_prime_degenerations(-1, 0, 8, D)[0][2]
        """

        vt = self._veering_triangulations[abs(level)][component]
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
            
            lc = [(-abs(level), component + index) for index in range(len(list_comp))]
            ld = l_ds_g

            #construct paths
            target_vertices = [ds_graph.vertex_index(a[0]) for a in l_vt_edge]
            paths = tree_with_target(ds_graph, root=0, target_vertices=target_vertices)
            assert len(paths) == len(l_vt_edge)
            #return paths

            #transport mvt
            lmvt = [self.transport_along_path(-abs(level), component, path) for path in paths]
            assert len(lmvt) == len(l_vt_edge)

            #make vertical degeneration and compute all transitions under monodromy groups and level-wise permutations
            l_deg_connected_comps = []
            all_mvt = []
            
            for i, mvt in enumerate(lmvt):
                _, edges_up, edges_low = l_vt_edge[i]
                mvt = mvt.degeneration(-abs(level), component, edges_low=edges_low, edges_up=edges_up)
                mvt = mvt.prime_decomposition(-abs(level), component)
                
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
