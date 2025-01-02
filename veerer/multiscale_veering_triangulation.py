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
    
    l, h, ang = prong
    
    for v in vt.vertices():
        if h in v:
            v1 = v
    vh = [r_up[h] for h in v1]
    
    if min(vh) >= 0: #The case that vh is in f_up
        h = r_up[h]
        return (l, h, ang)
    else: #The case that vh is in f_low
        #step1: find the half-edge in f_low
         if max(r_up) == -1:
            return (l, r_low[h],ang)
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
            return (l - 1, r_low[h], ang)

def new_prong_matching(vt, f_low, r_low, r_up, level):
    
    nh = 2 * vt.num_edges()
    newpm = []
    lpoles = [] #the poles at nodes in f_low considered so far
    for h in range(nh):
        hh = vt.next_at_vertex(h)
        if r_up[h] >= 0 and r_low[hh] >= 0:
            #find the boundary face in f_low containing hh
            for f in f_low.boundary_faces():
                if r_low[hh] in f:
                    f_pole = f
            
            if f_pole not in lpoles:
                lpoles.append(f_pole)
                while (_num_vertical_separatrices_in_corner(vt, h) == 0) or (r_low[h] >= 0):
                    h = vt.previous_at_vertex(h)
                if _num_vertical_separatrices_in_corner(vt, h) > 0:
                    prong1 = (level, r_up[h], 0)
                    prong2 = track_prong(vt, r_up, r_low, prong1)
                    assert prong2[0] == level - 1
                    pm = [prong1, prong2]
                    newpm.append(pm)
    return newpm

class MultiscaleVeeringTriangulation:
    r"""
    Multi-scale Veering Triangulations.

    A *multi-scale veering triangulation* is a triangulation of a (nodal) surface such that the restriction to each irreducible component forms a veering triangulation. Additionally, it encodes the information at the nodes.

    INPUT:

    veering_triangulation : a list of veering triangulations of length N, where the veering triangulation at index i is at level -i.

    horizontal_nodes : a list of length N, where the i-th entry consists of horizontal nodes (might be empty) in the form 
    "(h1,h2)"
    , where the half-edges h1 and h2 are contained in the boundary face of simple poles.

    prong_matching : a list consistings of pairs (prong1,prong2) with
    prong1 = (level1, h1, angle1)
    prong2 = (level2, h2, angle2)
    where: 
    - level1 > level2
    - h1 is an half-edge at a zero of the veering triangulation 'vt1' at level1, and h2 is an hal-edge in a boundary face of the veering triangulation 'vt2' at level2
    - angle1 and angle2 are the indices of the vertical separatrices in the corner of h1 and h2 respectively satisfying that: 
    the angle1 is in [0, vt1._num_vertical_separatrices_in_corner(h1)],
    and the angle2 is in [0, vt2._num_vertical_separatrices_in_corner(h2)].

    EXAMPLES::

        sage: from veerer.veerer import VeeringTriangulation
        sage: from veerer.veerer.multiscale_veering_triangulation import *

    A multi-scale veering triangulation of two levels and two vertical nodes::

        sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
        sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
        sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
        sage: mvt0
        MultiscaleVeeringTriangulation(
          veering_triangulations=[
            VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)", "RBRBB"),
            VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(~5,6,7)(0:5)(~3:1)(4:4,5:4)", "BBRBBBRR")
          ],
          horizontal_nodes=[[], []]
          prong_matching=[[(0, '0', 0), (-1, '0', 1)], [(0, '2', 0), (-1, '5', 1)]],
        )
        sage: mvt0.is_abelian()
        True

    A multi-scale veering triangulation of two levels, two vertical nodes and two horizontal nodes::

        sage: vt10 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
        sage: vt11 = VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(~4:1)(~3:1)(2:1)(5:5)(~9:1)(~8:1)(7:1)","BBRBRBBRBR")
        sage: mvt1 = MultiscaleVeeringTriangulation([vt10,vt11],[[],["(~4,7)","(~3,~8)"]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
        sage: mvt1
        MultiscaleVeeringTriangulation(
          veering_triangulations=[
            VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)", "RBRBB"),
            VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(2:1)(~3:1)(~4:1)(5:5)(7:1)(~8:1)(~9:1)", "BBRBRBBRBR")
          ],
          horizontal_nodes=[[], ['(~4,7)', '(~3,~8)']]
          prong_matching=[[(0, '0', 0), (-1, '0', 1)], [(0, '2', 0), (-1, '5', 1)]],
        )
        sage: mvt1.is_abelian()
        False
    """

    __slots__ = ('_veering_triangulations', '_horizontal_nodes', '_prong_matching')

    def __init__(self, veering_triangulations=None, horizontal_nodes=None, prong_matching=None, check=True):
        
        if isinstance(veering_triangulations, list):
            self._veering_triangulations = []
            for vt in veering_triangulations:
                if isinstance(vt, VeeringTriangulation):
                    self._veering_triangulations.append(vt)
                else:
                    raise ValueError(f"'vt' (value: {vt}) is not an instance of the VeeringTriangulation.")
        else:
            raise ValueError("The 'veering_triangulations' must be a list.")
        
        if isinstance(horizontal_nodes, list):
            if len(horizontal_nodes) != len(self._veering_triangulations):
                raise ValueError("Miss information of horizontal nodes at some levels")
            
            self._horizontal_nodes = []
            for level in range(len(horizontal_nodes)):
                self._horizontal_nodes.append([])
                nodes = horizontal_nodes[level]

                # normalization of horizontal nodes
                if isinstance(nodes, str):
                    nodes = str_to_cycles(nodes)
                    for i in range(len(nodes)):
                        node = nodes[i]
                        for j in range(2):
                            h = node[j]
                            if h < 0:
                                h = -2 * h - 1
                            else:
                                h = 2 * h
                            node[j] = h
                        f0, f1 = self.horizontal_faces(level, node)
                        nodes[i] = sorted([min(f0), min(f1)])
                                        
                for node in nodes:
                    if check:
                        self._check_horizontal_node(level, node)
                    self._horizontal_nodes[level].append(node)
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
                level2, h2, ang = prong2
                vt = self._veering_triangulations[abs(level2)]
                last_ang = _num_vertical_separatrices_in_corner(vt, h2) - 1 #the valide range is between 1 and the number of vertical separatrices 
                while ang == last_ang:
                    hh2 = vt.previous_in_face(h2)
                    ang = 0
                    prong2 = (level2, hh2, ang)

                pm = [prong1, prong2]

                #Note that the resulting prong2 is always equivalent to the original prong2
                prongs1, prongs2 = self.local_prong_matching(pm)
                assert prongs1.index(prong1) == prongs2.index(prong2)
                
                # normalization of prong1
                filtered = [prong for prong in prongs1 if prong[2] == 0]
                prong1 = min(filtered, key=lambda x: x[0])
                prong2 = prongs2[prongs1.index(prong1)]
                
                self._prong_matching.append([prong1, prong2])
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
        r"""
        EXAMPLES::

            sage: from veerer.veerer import VeeringTriangulation
            sage: from veerer.veerer.multiscale_veering_triangulation import *
            sage: vt10 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
            sage: vt11 = VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(~4:1)(~3:1)(2:1)(5:5)(~9:1)(~8:1)(7:1)","BBRBRBBRBR")
            sage: node = "(8,~7)"
            sage: mvt = MultiscaleVeeringTriangulation([vt10,vt11],[[],[node]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            Traceback (most recent call last)
            ...
            ValueError: h=8 not on a boundary face
            sage: node = "(0,~7)"
            sage: mvt = MultiscaleVeeringTriangulation([vt10,vt11],[[],[node]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            Traceback (most recent call last)
            ...
            ValueError: The half-edge 0 is not in the face of simple pole
        """
        level = self._check_level(level)
        vt = self._veering_triangulations[abs(level)]
        h1, h2 = node

        if (vt.face_angle(h1) != 0):
            raise ValueError(f"The half-edge {h1} is not in the face of simple pole")
        elif (vt.face_angle(h2) != 0):
            raise ValueError(f"The half-edge {h2} is not in the face of simple pole")
        
        f0, f1 = self.horizontal_faces(level, node)
        if f0 == f1:
            raise ValueError(f"The half-edge {h1} and {h2} cannot be in the same face")
        for hh in f0:
            for hhh in f1:
                if vt._colouring[hh // 2] != vt._colouring[hhh // 2]:
                    raise ValueError(f"The boundary edges in two faces of {h1} and {h2} have different colors")

    def _check_local_prong_matching(self, pm):
        r"""
        EXAMPLES::

            sage: from veerer.veerer import VeeringTriangulation
            sage: from veerer.veerer.multiscale_veering_triangulation import *
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: pm = [(0,"0",4),(-1,"0",1)] 
            sage: mvt = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[pm])
            Traceback (most recent call last)
            ...
            ValueError: The angle label of (0, '0', 4) is out of the valid range [0, 3].
            sage: pm = [(0,"~3",0),(-1,"0",1)] 
            sage: mvt = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[pm])
            Traceback (most recent call last)
            ...
            ValueError: The corner of (0, '~3', 0) is not a red-blue corner
            sage: pm = [(0,"1",0),(-1,"0",1)] 
            sage: mvt = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[pm])
            Traceback (most recent call last)
            ...
            ValueError: The orders of the zero and pole are not matched
        """ 
        
        NN = len(self._veering_triangulations)
        prong1, prong2= pm
        
        l1, h1, a1 = prong1
        l2, h2, a2 = prong2            

        #check the levels are valid
        if (l1 > 0) or (l2 > 0) or (-l1 >= NN) or (-l2 >= NN):
            raise ValueError(f"The levels in {pm} are invalid")
        if (l1 <= l2):
            raise ValueError(f"The level of {prong1} should be greater than the level of {prong2}")

        vt1 = self._veering_triangulations[abs(l1)]
        vt2 = self._veering_triangulations[abs(l2)]
        
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
                if pm[0][0] == level:
                    v = self.vertical_nodes(pm)[0]
                    if v in l1:
                        raise ValueError(f"There are prongs at the same zero as {pm[0]}")
                    else:
                        l1.append(v)
                if pm[1][0] == level:
                    f = self.vertical_nodes(pm)[1]
                    if f in l2:
                        raise ValueError(f"There are prongs at the same pole as {pm[1]}")
                    else:
                        l2.append(f)

    def __str__(self):
        
        vt_strings = ",\n    ".join(str(vt) for vt in self._veering_triangulations)

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
        vt = self.veering_triangulation_at_level(level)
        for f in vt.boundary_faces(): 
            if node[0] in f:
                f0 = f
            if node[1] in f:
                f1 = f
        return (f0, f1)

    def horizontal_nodes_at_level(self, i):
        r"""
        Return the list of horizontal nodes at the level of the input 'i'.

        Each node is represented by a triple (i,face0,face1).

        EXAMPLES::

            sage: from veerer.veerer import VeeringTriangulation
            sage: from veerer.veerer.multiscale_veering_triangulation import *
            sage: vt10 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
            sage: vt11 = VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(~4:1)(~3:1)(2:1)(5:5)(~9:1)(~8:1)(7:1)","BBRBRBBRBR")
            sage: mvt1 = MultiscaleVeeringTriangulation([vt10,vt11],[[],["(~4,7)","(~3,~8)"]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt1.horizontal_nodes_at_level(-1)
            [(-1, [9], [14]), (-1, [7], [17])]
            sage: mvt1.horizontal_nodes_at_level(0)
            []
        """

        l = self._horizontal_nodes[abs(i)]
        list_horiz_nodes = []
        if len(l) != 0:
            for node in l:
                f0, f1 = self.horizontal_faces(i, node)
                list_horiz_nodes.append((i,f0,f1))

        return list_horiz_nodes
    
    def horizontal_nodes(self):
        r"""
        Return all the horizontal nodes.

        Each node is expressed as (level,face0,face1)
        """

        NN = self.num_levels()
        l = []
        for i in range(NN):
            l = l + self.horizontal_nodes_at_level(-i)
        return l
    
    def vertical_nodes(self, pm):
        r"""
        Return the underlying node of the prong matching.

        The vertical node is represented as a pair of zero and face
        """
        p1, p2 = pm
        l1, h1, _ = p1
        l2, h2, _ = p2
        vt1 = self.veering_triangulation_at_level(l1)
        vt2 = self.veering_triangulation_at_level(l2)
        for v in vt1.vertices():
            if h1 in v:
                v1 = v
        for f in vt2.boundary_faces():
            if h2 in f:
                f1 = f
        return (v1, f1)
    
    def local_prong_matching(self, pm):
        r"""
        Returns the local prong matching at a vertical node.

        The input vertical node is represented by a tube (l1,v,l2,f), where v is the vertex of level-l1 veering triangulation, and f is the boundary face of level-l2 veering triangulation
        
        The output prong matching is represented as a list containing two sublists: [prongs1, prongs2].
        Each sublist 'prongsi' is a list of prongs, where each prong is represented as a tuple: (level, half_edge, angle_data).
        The angle_data specifies which prong within the corner of the half_edge is being referred to.
        Prongs with the same index in the two sublists are matched.

        EXAMPLES::

            sage: from veerer.veerer import VeeringTriangulation
            sage: from veerer.veerer.multiscale_veering_triangulation import *
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt0.vertical_nodes_between_levels(-1,0)
            [(0, [0, 7], -1, [0]), (0, [3, 4], -1, [8, 10])]
            sage: mvt0.local_prong_matching((0, [0, 7], -1, [0]))
            [[(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3)],
            [(-1, 0, 1), (-1, 0, 2), (-1, 0, 3), (-1, 0, 0)]]
            sage: mvt0.local_prong_matching((0, [3, 4], -1, [8, 10]))
            [[(0, 4, 0), (0, 4, 1), (0, 4, 2), (0, 4, 3), (0, 4, 4), (0, 4, 5)],
            [(-1, 10, 1), (-1, 10, 2), (-1, 8, 0), (-1, 8, 1), (-1, 8, 2), (-1, 10, 0)]]
        """
        
        p1, p2 = pm
        l1, h1, _ = p1
        l2, h2, _ = p2

        vt1 = self.veering_triangulation_at_level(l1)
        vt2 = self.veering_triangulation_at_level(l2)
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
                    prongs1.append((l1,h,0))
            else:
                num_p = _num_vertical_separatrices_in_corner(vt1, h)
                for j in range(num_p):
                    prongs1.append((l1,h,j))
        
        #compute the list of prongs at the pole
        pole.reverse()
        for h in pole:
            num_p = _num_vertical_separatrices_in_corner(vt2, h) - 1
            for j in range(num_p):
                    prongs2.append((l2,h,j))

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

        EXAMPLES::

            sage: from veerer.veerer import VeeringTriangulation
            sage: from veerer.veerer.multiscale_veering_triangulation import *
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt0.vertical_nodes_between_levels(-1,0)
            [(0, [0, 7], -1, [0]), (0, [3, 4], -1, [8, 10])]
            sage:mvt0.prong_matching_map((0, 4, 1))
            (-1, 10, 2)
        """
        level, h, a = prong
        nodes = self.vertical_nodes()
        for node in nodes:
            l1, v, l2, f = node
            if (l1 == level) and (h in v):
                prongs1, prongs2 = self.local_prong_matching(node)
                assert prong in prongs1
                j = prongs1.index(prong)
                return prongs2[j]
            if (l2 == level) and (h in f):
                prongs1, prongs2 = self.local_prong_matching(node)
                assert prong in prongs2
                j = prongs2.index(prong)
                return prongs1[j]
            
    def components_have_horiztal_nodes_with(self, level, comp_index):
        r"""
        Return the indices of the components that have horizontal nodes with the input component
        """
        vt = self.veering_triangulation_at_level(level)
        l_node = self.horizontal_nodes_at_level(level)
        
        l = []
        
        for i, f1, f2 in l_node:
            #compute the component indices of the face f1 and f2
            c1 = in_connected_component(vt, f1[0])
            c2 = in_connected_component(vt, f2[0])
            
            if c1 == comp_index:
                if (level,c2) not in l:
                    l.append((level,c2))
            if c2 == comp_index:
                if (level,c1) not in l:
                    l.append((level,c1))
        return l
    
    def is_abelian(self, certificate=False):
        r"""
        Return whether the multi-scale veering triangulation is Abelian. 

        EXAMPLES::

            sage: from veerer.veerer import VeeringTriangulation
            sage: from veerer.veerer.multiscale_veering_triangulation import *

        A horizontal node between the same components::

            sage: vt = VeeringTriangulation("(0,1,4)(~4,2,3)(~0:1)(~1:1)(~2:1)(~3:1)","RBBRR")
            sage: mvt = MultiscaleVeeringTriangulation([vt],["(~1,~2)"],[])
            sage: mvt.is_abelian()
            False

        Horizontal nodes between different components::
            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0:1)(~2:1)(~1:1)(~3:1)(~5:1)(~4:1)(~6:1)(~8:1)(~7:1)","RBRRBRRBR")
            sage: mvt = MultiscaleVeeringTriangulation([vt],["(~2,~5)(~1,~3)"],[])
            sage: mvt.is_abelian()
            False
            sage: mvt = MultiscaleVeeringTriangulation([vt],["(~2,~5)(~1,~6)"],[])
            sage: mvt.is_abelian()
            True

        Mix of horizontal and vertical nodes::
            sage: vt0 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
            sage: vt1 = VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(~4:1)(~3:1)(2:1)(5:5)(~9:1)(~8:1)(7:1)","BBRBRBBRBR")
            sage: vt0.is_abelian()
            True
            sage: vt1.is_abelian()
            True
            sage: mvt0 = MultiscaleVeeringTriangulation([vt0,vt1],[[],"(~4,7)"],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt0.is_abelian()
            False
            sage: mvt1 = MultiscaleVeeringTriangulation([vt0,vt1],[[],"(~3,~8)"],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: print(mvt1.is_abelian(certificate=True))
            (True, [[True, False, True, False, False, True, False, True, False, True], [False, True, False, True, False, True, False, True, False, True, True, False, True, False, True, False, True, False, True, False]])
        """

        NN = self.num_levels()
        oris = [[]] * NN
        
        #Step1: propagate level-wise
        for i in range(NN):
            vt = self.veering_triangulation_at_level(-i)
            abelian, l = vt.is_abelian(certificate=True)
            if abelian:
                oris[i] = l
            else:
                return (False, None) if certificate else False
        
        #Step2: propagate through horizontal nodes
        for i in range(NN):
            vt = self.veering_triangulation_at_level(-i)
            l_component = vt.connected_components()
            
            lo = oris[i]
            ne = len(lo)
            
            l_nodes = self.horizontal_nodes_at_level(-i)
            lc = [] #the list of components in the level-(-i) adjusted so far
            
            for level, f1, f2 in l_nodes:
                # find out the components containing the matched poles
                c1 = in_connected_component(vt, f1[0])
                c2 = in_connected_component(vt, f2[0])
                        
                if lo[f1[0]] == lo[f2[0]]:
                    #check the coherence
                    if c1 == c2:
                        return (False, None) if certificate else False

                    if (c1 in lc) and (c2 in lc):
                        return (False, None) if certificate else False
                    
                    if c1 not in lc:
                        #rotate the component c1 by pi
                        for h in range(ne):
                            if h // 2 in l_component[c1]:
                                lo[h] = not lo[h]
                        #add coherent components
                        lc.append(c1)
                        if c2 not in lc:
                            lc.append(c2)
                    elif c2 not in lc:
                        #rotate the component c2 by pi
                        for h in range(ne):
                            if h // 2 in l_component[c2]:
                                lo[h] = not lo[h]
                        
                        lc.append(c2)
                else:
                    #add coherent components
                    if c1 not in lc:
                        lc.append(c1)
                    if c2 not in lc:
                        lc.append(c2)
            
            oris[i] = lo
            
        #Step3: propagate through vertical nodes
        
        lv = [] #the list of component adjusted so far, where the component is labeled by (level, index of the component in this level) 
        
        for pm in self._prong_matching:
            
            level1, h1, ang1 = pm[0]
            level2, h2, ang2 = pm[1]
            
            vt1 = self.veering_triangulation_at_level(level1)
            vt2 = self.veering_triangulation_at_level(level2)
            
            o1 = oris[-level1][h1]
            o2 = oris[-level2][h2]
            
            #decide the orietation of the prong pm[0]
            if (ang1)%2 == 1:
                o1 = not o1
            
            #decide the orietation of the prong pm[1]
            if (ang2)%2 == 1:
                o2 = not o2 
            
            #find the labels of the components where the prongs are. 
            #the labels are in the form: (level, index of the component in this level)
            #moreover find out all the components that have horizontal nodes with the components containing the prongs
            c1 = in_connected_component(vt1, h1) 
            l1 = self.components_have_horiztal_nodes_with(level1, c1)
            if (level1, c1) not in l1:
                l1.append((level1, c1))
            
            c2 = in_connected_component(vt2, h2)
            l2 = self.components_have_horiztal_nodes_with(level2, c2)
            if (level2, c2) not in l2:
                l2.append((level2, c2))
            
            #adjust the components
            lo1 = oris[-level1]
            n1 = len(lo1)
            lo2 = oris[-level2]
            n2 = len(lo2)
            
            if o1 != o2:#incoherent
                if ((level1, c1) in lv) and ((level2, c2) in lv):
                    return (False, None) if certificate else False
                
                if (level1, c1) not in lv:
                    #rotate all the components in l1 by pi
                    for h in range(n1):
                        c = in_connected_component(vt1, h)
                        if (level1, c) in l1:
                            lo1[h] = not lo1[h]
                        
                        for label in l1:
                            lv.append(label)
                        
                        if (level2, c2) not in lv:
                            for label in l2:
                                lv.append(label)
                
                elif (level2, c2) not in lv:
                    #rotate all the components in l2 by pi
                    for h in range(n2):
                        c = in_connected_component(vt2, h)
                        if (level2, c) in l2:
                            lo2[h] = not lo2[h]
                        
                        for label in l2:
                            lv.append(label)
            else: #coherent orietation
                if (level1, c1) not in lv:
                    for label in l1:
                        lv.append(label)
                if (level2, c2) not in lv:
                    for label in l2:
                        lv.append(label)
            
            oris[-level1] = lo1
            oris[-level2] = lo2
                
        return (True, oris) if certificate else True
    
    def degeneration(self, level, edges_low=None, edges_up=None):
        r"""
        Return the multi-scale veering triangulation by blowing-up the given subset of ``edge``.

        This corresponds to an either a horizontal degeneration or a vertical degeneration in the BCGGM compactification.

        EXAMPLES::

            sage: from veerer import *
            sage: from veerer.multiscale_veering_triangulation import *
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt0.degeneration(0, edges_low=[2], edges_up=[0, 1, 3, 4])
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulationLinearFamily("(~0,~2,~1)(0:3,1:1,2:6)", "RBB", [(1, 0, 1), (0, 1, 1)]),
                VeeringTriangulationLinearFamily("(0:6,~0:2)", "R", [(1)]),
                VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(~5,6,7)(0:5)(~3:1)(4:4,5:4)", "BBRBBBRR")
            ],
            horizontal_nodes=[[], [], []]
            prong_matching=[((0, 0, 0), (-2, 0, 1)), ((-1, 0, 0), (-2, 10, 1)), ((0, 4, 0), (-1, 0, 0))],
            )

            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt0.degeneration( -1, edges_low=[0, 1, 2, 3, 4, 5], edges_up=[6, 7])
            MultiscaleVeeringTriangulation(
            veering_triangulations=[
                VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)", "RBRBB"),
                VeeringTriangulationLinearFamily("(~0,1,2)(~1,~2,3)(0:5)(~3:1)(4:4,5:4)(~4:1)(~5:1)", "BBRBBB", [(1, 0, 1, 1, 0, 0), (0, 1, -1, 0, 0, 0), (0, 0, 0, 0, 1, 1)])
            ],
            horizontal_nodes=[[], [[9, 11]]]
            prong_matching=[((0, 0, 0), (-1, 0, 1)), ((0, 4, 0), (-1, 10, 1))],
            )
        """

        vt = self.veering_triangulation_at_level(level)
        nh = 2 * (vt.num_edges())
        ep = vt.edge_permutation()
    
        f_up ,f_low, r_up, r_low = vt.degeneration(edges_low=edges_low, edges_up=edges_up, collapsed_half_edge_relabelling=True)
        
        #build list of veering triangulations
        vts = self._veering_triangulations.copy()
        if f_up is None:
            vts[abs(level)] = f_low
        else:
            vts[abs(level)] = f_up
            vts.insert(abs(level) + 1, f_low)
        
        #build the horizontal nodes
        l1 = []
        l_horiz = self._horizontal_nodes.copy()
        #existing horizontal nodes
        for a1, a2 in self._horizontal_nodes[abs(level)]:
            a1 = r_low[a1]
            a2 = r_low[a2]
            l1.append([a1,a2])
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
                    node = sorted([b1, b2])
                    if node not in l1:
                        l1.append(node)
            l_horiz[abs(level)] = l1
        else:
            l_horiz.append([])
        
        #build the vertical nodes
        l_pm = []
        #existing vertical nodes
        original_pm = self._prong_matching.copy()
        for pm in original_pm:
            prong1, prong2 = pm
            if prong1[0] == level:
                prong1 = track_prong(vt, r_up, r_low, prong1)
                if f_up is None:
                    l_pm.append([prong1,prong2])
                else:
                    prong2 = (prong2[0] - 1, prong2[1], prong2[2])
                    l_pm.append([prong1,prong2])
            elif prong2[0] == level:
                prong2 = track_prong(vt, r_up, r_low, prong2)
                l_pm.append([prong1,prong2])
            else:
                l_pm.append(pm)
        #new vertical nodes
        if f_up is not None:
            l_pm  = l_pm + new_prong_matching(vt, f_low, r_low, r_up, level)
        
        #build the degeneration
        return MultiscaleVeeringTriangulation(vts,l_horiz,l_pm)