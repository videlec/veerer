r"""
Multi-scalle Veering Triangulations
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
    if isinstance(halfedge, str):
        halfedge = str_to_label(halfedge)

    col = vt._colouring
    h1 = vt.vertex_permutation()[halfedge]
    a = vt.boundary_vector()[halfedge]
    
    if a == 0:
        raise ValueError('the halfedge is not boundary')
    
    if (col[halfedge // 2] == RED) and (col[h1 // 2] == BLUE):
        num = a + 1
    else:
        num = a
    
    return num

def _num_lower_prongs_in_corner(vt,halfedge):
    r"""
    Return the number of valid prongs in the corner of the half-edge.
     
    This specific number is used later to construct a valid prong. The boundary face containing the input half-edge should be regarded as the pole of a vertical node.

    Comparing to the method '_num_vertical_separatrices', we only count the red-blue colouring changes in the 'interior' of the corner.
    """
    alpha = vt.boundary_vector()
    if alpha[halfedge] == 0:
        raise ValueError("The half-edge is not boundary")
    
    vp = vt.vertex_permutation()
    col = vt._colouring

    hh = vp[halfedge]
    num_p = _num_vertical_separatrices_in_corner(vt, halfedge)
    if (col[halfedge // 2] == RED) and (col[hh // 2] == RED):
        return num_p - 1
    elif (col[halfedge // 2] == RED) and (col[hh // 2] == BLUE):
        return num_p - 2
    elif (col[halfedge // 2] == BLUE) and (col[hh // 2] == BLUE):
        return num_p - 1
    elif (col[halfedge // 2] == BLUE) and (col[hh // 2] == RED):
        return num_p

def in_connected_component(vt, h):
    r"""
    Return the index of the component which contains the half-edge h in the list vt.connected_components()
    """
    l_comp = vt.connected_components()
    for comp in l_comp:
        if (h // 2) in comp:
            return l_comp.index(comp)


class MultiscaleVeeringTriangulation:
    r"""
    Multi-scale Veering Triangulations.

    A *multi-scale veering triangulation* is a triangulation of a (nodal) surface such that the restriction to each irreducible component forms a veering triangulation. Additionally, it encodes the information at the nodes.

    INPUT:

    veering_triangulation : a list of veering triangulations of length N, where the veering triangulation at index i are at level -i.

    horizontal_nodes : a list of length N, where the i-th entry consists of horizontal nodes (might be empty) in the form 
    "(h1,h2)"
    , where the half-edges h1 and h2 are contained in the boundary face of simple poles.

    prong_matching : a list consistings of pairs (prong1,prong2) with
    prong1 = (level1, h1, angle1)
    prong2 = (level2, h2, angle2)
    where: 
    - level1 > level2
    - h1 is an half-edge at a zero of the veering triangulation 'vt1' at level1, and h2 is an hal-edge in a boundary face of the veering triangulation 'vt2' at level2
    - angle1 and angle 2 are the indices of the vertical separatrices in the corner of h1 and h2 respectively satisfying that: 
    angle1 is in [0, vt1._num_vertical_separatrices_in_corner(h1)],
    and angle2 is in [0, vt2._num_lower_prongs_in_corner(h2)]

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
            for l in range(len(horizontal_nodes)):
                self._horizontal_nodes.append([])
                level = -l
                for node in horizontal_nodes[l]:
                    if check:
                        self._check_horizontal_node(level, node)
                    self._horizontal_nodes[l].append(node)
        else:
            raise ValueError("The 'horizontal_nodes' must be a list.")
        
        if isinstance(prong_matching, list):
            self._prong_matching = []
            for pm in prong_matching:
                if check:
                    self._check_prong_matching(pm)
                self._prong_matching.append(pm)
        else:
            raise ValueError("The 'prong_matching' must be a list.")
    
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
        #check if the horizontal nodes are valid.
        vt = self._veering_triangulations[abs(level)]
        
        b1, b2 = node.strip("()").split(",")
        h1 = str_to_label(b1)
        h2 = str_to_label(b2)

        if (vt.face_angle(h1) != 0):
            raise ValueError(f"The half-edge {b1} is not in the face of simple pole")
        elif (vt.face_angle(h2) != 0):
            raise ValueError(f"The half-edge {b2} is not in the face of simple pole")

    def _check_prong_matching(self, pm):
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
        
        l1, str1, a1 = prong1
        l2, str2, a2 = prong2            
        h1 = str_to_label(str1)
        h2 = str_to_label(str2)

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
            raise ValueError("The orders of the zero and pole are not matched")
        
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
            num_p = _num_lower_prongs_in_corner(vt2,h2)
            if a2 not in range(num_p):
                raise ValueError(f"The angle label of {prong2} is out of the valid range [0, {num_p - 1}].")

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

    def veering_triangulation_at_level(self, i):
        if i > 0:
            raise ValueError('levels are non-positive')
        return self._veering_triangulations[abs(i)]
    
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
        vt = self.veering_triangulation_at_level(i)
        list_faces = vt.boundary_faces()

        list_horiz_nodes = []

        if len(l) != 0:
            for c in l:
                cc = str_to_cycles(c)[0]
                cc1 = []

                #turn the strings of the edges into the labels
                for j in range(2):
                    if cc[j] < 0:
                        cc1.append(2*abs(cc[j]) - 1)
                    else:
                        cc1.append(2*cc[j])
                
                #find the faces containing the half-edges
                for f in list_faces: 
                    if cc1[0] in f:
                        f0 = f
                    if cc1[1] in f:
                        f1 = f
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
    
    def vertical_nodes_between_levels(self,i,j):
        r"""
        Return the vertical nodes between level i and level j.

        If i<j, each vertical node is represented by a tupe (i,v,j,f), where v is the vertex in level-i veering triangulation, and f is the boundary face in the level-j veering triangulation

        EXAMPLES::

            sage: from veerer.veerer import VeeringTriangulation
            sage: from veerer.veerer.multiscale_veering_triangulation import *
            sage: vt00 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:5,3:1)","RBRBB")
            sage: vt01 = VeeringTriangulation("(~0,1,2)(~1,~2,3)(~4,~6,~7)(6,7,~5)(0:5)(~3:1)(4:4,5:4)","BBRBBBRR")
            sage: mvt0 = MultiscaleVeeringTriangulation([vt00,vt01],[[],[]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt0.vertical_nodes_between_levels(-1,0)
            [(0, [0, 7], -1, [0]), (0, [3, 4], -1, [8, 10])]
            sage: mvt0.vertical_nodes_between_levels(0,-1)
            [(0, [0, 7], -1, [0]), (0, [3, 4], -1, [8, 10])]
        """
    
        list_pm = self._prong_matching
        
        if i == j:
            raise ValueError('vertical nodes are between different levels')
        else:
            l1, l2 = sorted([i,j], reverse=True) #l1 > l2
        
        vt1 = self.veering_triangulation_at_level(l1)
        vt2 = self.veering_triangulation_at_level(l2)
        list_vertices = vt1.vertices()
        list_bdry_faces = vt2.boundary_faces()
        
        l_vert_nodes = []
        
        for pm in list_pm:
            prong1, prong2 = pm
            ll1, h1, angle1 = prong1
            ll2, h2, angle2 = prong2
            if (ll1 == l1) and (ll2 == l2):
                
                label_h1 = str_to_label(h1)
                label_h2 = str_to_label(h2)

                #find out the vertices and faces
                for v in list_vertices:
                    if label_h1 in v:
                        v1 = v
                        break
                for f in list_bdry_faces:
                    if label_h2 in f:
                        f1 = f
                        break
                l_vert_nodes.append((l1,v1,l2,f1))
        
        return l_vert_nodes
    
    def vertical_nodes(self):
        r"""
        Return all the vertical nodes
        """
        vnodes = []
        NN = self.num_levels()
        for i in range(NN - 1):
            for j in range(i + 1, NN):
                vnodes = vnodes + self.vertical_nodes_between_levels(0,-1)
        
        return vnodes
    
    def local_prong_matching(self, vertical_nodes):
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
        l1, zero, l2, pole = vertical_nodes
        
        vt1 = self.veering_triangulation_at_level(l1)
        vt2 = self.veering_triangulation_at_level(l2)
        alpha1 = vt1.boundary_vector()
        
        vp1 = vt1.vertex_permutation()
        vp2 = vt2.vertex_permutation()
        
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
            hh = vp2[h]
            num_p = _num_lower_prongs_in_corner(vt2, h)
            for j in range(num_p):
                    prongs2.append((l2,h,j))
        
        assert len(prongs1) == len(prongs2)
        
        # match the prongs. Shift the lists so that the corresponding indices are matched.
        list_pm = self._prong_matching
        for pm in list_pm:
            p1, p2 = pm
            level1, string1, angle1 = p1
            level2, string2, angle2 = p2
            h1 = str_to_label(string1)
            h2 = str_to_label(string2)
            pp1 = (level1, h1, angle1)
            pp2 = (level2, h2, angle2)
            
            if (pp1 in prongs1) and (pp2 in prongs2):
                index1 = prongs1.index(pp1)
                shiftprong1 = prongs1[index1:] + prongs1[:index1]
                
                index2 = prongs2.index(pp2)
                shiftprong2 = prongs2[index2:] + prongs2[:index2]
                break
        
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
        l_comp = vt.connected_components()
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
            sage: mvt = MultiscaleVeeringTriangulation([vt],[["(~1,~2)"]],[])
            sage: mvt.is_abelian()
            False

        Horizontal nodes between different components::
            sage: vt = VeeringTriangulation("(0,1,2)(3,4,5)(6,7,8)(~0:1)(~2:1)(~1:1)(~3:1)(~5:1)(~4:1)(~6:1)(~8:1)(~7:1)","RBRRBRRBR")
            sage: mvt = MultiscaleVeeringTriangulation([vt],[["(~2,~5)","(~1,~3)"]],[])
            sage: mvt.is_abelian()
            False
            sage: mvt = MultiscaleVeeringTriangulation([vt],[["(~2,~5)","(~1,~6)"]],[])
            sage: mvt.is_abelian()
            True

        Mix of horizontal and vertical nodes::
            sage: vt0 = VeeringTriangulation("(~0,~3,4)(~1,~4,~2)(0:3,1:1,2:3,3:1)","RBRBB")
            sage: vt1 = VeeringTriangulation("(~0,1,4)(~1,~2,3)(~5,6,9)(~6,~7,8)(0:5)(~4:1)(~3:1)(2:1)(5:5)(~9:1)(~8:1)(7:1)","BBRBRBBRBR")
            sage: vt0.is_abelian()
            True
            sage: vt1.is_abelian()
            True
            sage: mvt0 = MultiscaleVeeringTriangulation([vt0,vt1],[[],["(~4,7)"]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: mvt0.is_abelian()
            False
            sage: mvt1 = MultiscaleVeeringTriangulation([vt0,vt1],[[],["(~3,~8)"]],[[(0,"0",0),(-1,"0",1)],[(0,"2",0),(-1,"5",1)]])
            sage: print(mvt11.is_abelian(certificate=True))
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
            lc = [] #the list of components in the level-i adjusted so far
            
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
            
            level1, str1, ang1 = pm[0]
            level2, str2, ang2 = pm[1]
            h1 = str_to_label(str1)
            h2 = str_to_label(str2)
            
            vt1 = self.veering_triangulation_at_level(level1)
            vt2 = self.veering_triangulation_at_level(level2)
            
            o1 = oris[-level1][h1]
            o2 = oris[-level2][h2]
            
            #decide the orietation of the prong pm[0]
            if (ang1)%2 == 1:
                o1 = not o1
            
            #decide the orietation of the prong pm[1]
            if vt2._colouring[h2 // 2] == RED:
                if (ang2)%2 == 0:
                    o2 = not o2
            elif vt2._colouring[h2 // 2] == BLUE:
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
    
