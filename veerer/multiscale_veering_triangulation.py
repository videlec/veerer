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

from .permutation import perm_check, perm_cycles, perm_cycles_to_string, str_to_cycles, str_to_cycles_and_data
from .triangulation import Triangulation
from .veering_triangulation import *
from .constants import *
from .polyhedron import *


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
                    vert_sep = ((level, comp), h, 0)
                    prong1 = ((level,comp), r_up[h], 0)
                    prong2 = track_prong(vt, r_up, r_low, vert_sep)
                    assert prong2[0][0] == level - 1
                    pm = [prong1, prong2]
                    newpm.append(pm)
                    lpoles.append(f_pole)
    return newpm

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
        horizontal_nodes=[[], []]
        prong_matching=[[((0, 0), 0, 0), ((-1, 0), 0, 0)], [((0, 0), 10, 0), ((-1, 0), 4, 0)]],
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

    __slots__ = ('_veering_triangulations', '_horizontal_nodes', '_prong_matching')

    def __init__(self, veering_triangulations=None, horizontal_nodes=None, prong_matching=None, check=True):
        
        if isinstance(veering_triangulations, list):
            self._veering_triangulations = []
            for l in veering_triangulations:
                level = veering_triangulations.index(l)
                if isinstance(l, VeeringTriangulation):
                    self._veering_triangulations.append([l])
                elif isinstance(l, list):
                    self._veering_triangulations.append([])
                    for vt in l:
                        if isinstance(vt, VeeringTriangulation):
                            self._veering_triangulations[level].append(vt)
                        else:
                            raise ValueError(f"'vt' (value: {vt}) is not an instance of the VeeringTriangulation.")
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
            f"  horizontal_nodes={horizontal_nodes_str}\n"
            f"  prong_matching={prong_matching_str},\n"
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

    def num_levels(self):
        return len(self._veering_triangulations)

    def veering_triangulation_at_level(self, level):
        level = self._check_level(level)
        return self._veering_triangulations[level]
    
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

            sage: from veerer import VeeringTriangulation
            sage: from veerer.multiscale_veering_triangulation import *
            sage: vt10 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
            sage: vt11 = VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(~4:1)(~3:1)(2:1)(5:5)(~9:1)(~8:1)(7:1)","BBRBRBBRBR")
            sage: mvt1 = MultiscaleVeeringTriangulation([vt10,vt11],[[],[[(0,"~4"),(0,"7")],[(0,"~3"),(0,"~8")]]],[[((0,0),"0",0),((-1,0),"0",1)],[((0,0),"2",0),((-1,0),"5",1)]])
            sage: mvt1.horizontal_nodes_at_level(-1)
            [(-1, 0, [7], 0, [17]), (-1, 0, [9], 0, [14])]
            sage: mvt1.horizontal_nodes_at_level(0)
            []
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

            sage: from veerer import VeeringTriangulation
            sage: from veerer.multiscale_veering_triangulation import *

        A horizontal node between the same components::

            sage: vt = VeeringTriangulation("(0,1,4)(~4,2,3)(~0:1)(~1:1)(~2:1)(~3:1)","RBBRR")
            sage: mvt = MultiscaleVeeringTriangulation([vt],[[[(0,"~1"),(0,"~2")]]],[])
            sage: mvt.is_abelian()
            False

        Mix of horizontal and vertical nodes::
            sage: vt0 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
            sage: vt1 = VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(~4:1)(~3:1)(2:1)(5:5)(~9:1)(~8:1)(7:1)","BBRBRBBRBR")
            sage: vt0.is_abelian()
            True
            sage: vt1.is_abelian()
            True
            sage: mvt0 = MultiscaleVeeringTriangulation([vt0,vt1],[[],[[(0,"~4"),(0,"7")]]],[[((0,0),"0",0),((-1,0),"0",1)],[((0,0),"2",0),((-1,0),"5",1)]])
            sage: mvt0.is_abelian()
            False
            sage: mvt1 = MultiscaleVeeringTriangulation([vt0,vt1],[[],[[(0,"~3"),(0,"~8")]]],[[((0,0),"0",0),((-1,0),"0",1)],[((0,0),"2",0),((-1,0),"5",1)]])
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
            horizontal_nodes=[[], [[(0, 9), (0, 11)]]]
            prong_matching=[[((0, 0), 0, 0), ((-1, 0), 0, 1)], [((0, 0), 4, 0), ((-1, 0), 10, 1)]],
            )
        """

        vt = self._veering_triangulations[abs(level)][component]
        nh = 2 * (vt.num_edges())
        ep = vt.edge_permutation()
    
        f_up ,f_low, r_up, r_low = vt.degeneration(edges_low=edges_low, edges_up=edges_up, collapsed_half_edge_relabelling=True)
        
        #build list of veering triangulations. 
        # TO BE CONFIRMED: there are choices of the component in the original level ``level`` in the new levels. However, since we will consider all possible vertical degenerations, we could consider just one case that their levels remain the same. 
        vts = self._veering_triangulations.copy()
        
        if f_up is None:
            vts[abs(level)][component] = f_low
            l_vts = [vts]
        else:
            vts[abs(level)][component] = f_up
            vts.insert(abs(level) + 1, [f_low])
        
        #build the horizontal nodes
        l1 = []
        l_horiz = self._horizontal_nodes.copy()
        #existing horizontal nodes
        for a1, a2 in self._horizontal_nodes[abs(level)]:
            c1, h1 = a1
            c2, h2 = a2
            h1 = r_low[h1]
            h2 = r_low[h2]
            l1.append([(c1, h1),(c2, h2)])
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
        
        #build the vertical nodes
        l_pm = []
        #existing vertical nodes
        original_pm = self._prong_matching.copy()
        for pm in original_pm:
            prong1, prong2 = pm
            if prong1[0] == (level, component):
                prong1 = track_prong(vt, r_up, r_low, prong1)
                if f_up is None:
                    l_pm.append([prong1,prong2])
                else:
                    prong2 = ((prong2[0][0] - 1,prong2[0][1]), prong2[1], prong2[2])
                    l_pm.append([prong1,prong2])
            elif prong2[0] == (level, component):
                prong2 = track_prong(vt, r_up, r_low, prong2)
                l_pm.append([prong1,prong2])
            else:
                l_pm.append(pm)
        #new vertical nodes
        if f_up is not None:
            l_pm  = l_pm + _new_prong_matching(vt, f_low, r_up, r_low,level,component)

        #build the degeneration
        return MultiscaleVeeringTriangulation(vts,l_horiz,l_pm)