r"""
Paths in Delaunay-Strebel graph and monodromy of linear subvarieties.
"""

from collections import deque

from sage.misc.prandom import choice, randrange

from veerer.constants import BLUE, RED, HORIZONTAL, VERTICAL
from veerer.permutation import perm_preimage


class DiGraphPath:
    r"""
    Path in a DiGraph.

    EXAMPLES::

        sage: from veerer.delaunay_strebel_path import DiGraphPath
        sage: G = digraphs.ButterflyGraph(5)
        sage: path = DiGraphPath(G, ('01000', 0))
        sage: path.append(('11000', 1))
        sage: path.append(('11000', 0), reverse=True)
        sage: path.appendleft(('01000', 1), reverse=True)
        sage: path.appendleft(('11000', 0))
        sage: path
        Closed path of length 4 in 5-dimensional Butterfly at ('11000', 0)
    """
    def __init__(self, graph, start):
        self._graph = graph
        self._vertices = deque([start])  # vertices
        self._edge_labels = deque([])    # edge labels
        self._signs = deque([])          # 1 if edge is taken backward

    def copy(self):
        ans = type(self).__new__(type(self))
        ans._vertices = self._vertices[:]
        ans._edge_labels = self._edge_labels[:]
        ans._signs = self._signs[:]
        return ans

    def __bool__(self):
        return bool(self._edge_labels)

    def __len__(self):
        return len(self._edge_labels)

    def __repr__(self):
        if self.is_closed():
            return "Closed path of length {} in {} at {}".format(len(self), self._graph, self.start())

        else:
            return "Path of length {} in {} from {} to {}".format(len(self), self._graph, self.start(), self.end())

    def start(self):
        return self._vertices[0]

    def end(self):
        return self._vertices[-1]

    def __invert__(self):
        ans = self.copy()
        ans._vertices.reverse()
        ans._edges.reverse()
        ans._signs.reverse()
        for i, s in ans._signs:
            ans[i] = 1 - s

    def __mul__(self, other):
        if type(self) != type(other):
            raise TypeError

        ans = self.copy()
        ans._vertices.extend(other._vertices[1:])
        ans._edge_labels.extend(other._edge_labels)
        ans._signs.extend(other._signs)
        return ans

    def append(self, target=None, edge_label=None, reverse=False):
        source = self.end()
        if target is None:
            if reverse:
                for (target2, _, edge_label2) in self._graph.incoming_edges(source):
                    if edge_label == edge_label2:
                        target = target2
                        break
            else:
                for (_, target2, edge_label2) in self._graph.outgoing_edges(source):
                    if edge_label == edge_label2:
                        target = target2
                        break
            if target is None:
                raise ValueError("invalid edge_label={} from {}".format(edge_label, source))
        if edge_label is None:
            if reverse:
                edge_label = self._graph.edge_label(target, source)
            else:
                edge_label = self._graph.edge_label(source, target)
            if self._graph.allows_multiple_edges():
                if len(edge_label) != 1:
                    raise ValueError("invalid or ambiguous target")
                edge_label = edge_label[0]

        if reverse:
            assert self._graph.has_edge(target, source, edge_label)
        else:
            assert self._graph.has_edge(source, target, edge_label)

        self._vertices.append(target)
        self._edge_labels.append(edge_label)
        self._signs.append(int(reverse))

    def random_append(self, repeat=1, reverse=True):
        for _ in range(repeat):
            if reverse and randrange(2):
                reverse = True
                (target, _, edge_label) = choice(self._graph.incoming_edges(self.end()))
            else:
                reverse = False
                (_, target, edge_label) = choice(self._graph.outgoing_edges(self.end()))
            self.append(target, edge_label, reverse)

    def pop(self):
        r"""
        Pop the last edge of the path and return ``(source, target, edge_label)``.
        """
        if not self:
            raise IndexError("pop from an empty path")
        target = self._vertices.pop()
        edge_label = self._edge_labels.pop()
        return (self.end(), target, edge_label)

    def appendleft(self, source=None, edge_label=None, reverse=False):
        r"""
        Append an edge on the left.
        """
        target = self.start()
        if source is None:
            if reverse:
                for (_, source2, edge_label2) in self._graph.outgoing_edges(target):
                    if edge_label == edge_label2:
                        source = source2
                        break
            else:
                for (source2, _, edge_label2) in self._graph.incoming_edges(target):
                    if edge_label == edge_label2:
                        source = source2
                        break
            if source is None:
                raise ValueError("invalid edge_label={} to append left from {}".format(edge_label, target))
        if edge_label is None:
            if reverse:
                edge_label = self._graph.edge_label(target, source)
            else:
                edge_label = self._graph.edge_label(source, target)
                if self._graph.allows_multiple_edges():
                    if len(edge_label) != 1:
                        raise ValueError("invalid or ambiguous source")
                    edge_label = edge_label[0]

        if reverse:
            assert self._graph.has_edge(target, source, edge_label)
        else:
            assert self._graph.has_edge(source, target, edge_label)

        self._vertices.appendleft(source)
        self._edge_labels.appendleft(edge_label)
        self._signs.appendleft(int(reverse))

    def random_appendleft(self, repeat=1, reverse=True):
        for _ in range(repeat):
            if reverse and randrange(2):
                reverse = True
                (_, source, edge_label) = choice(self._graph.outgoing_edges(self.start()))
            else:
                reverse = False
                (source, _, edge_label) = choice(self._graph.incoming_edges(self.start()))
            self.appendleft(source, edge_label, reverse)

    def popleft(self):
        r"""
        Pop the first edge of the path and return ``(source, target, edge_label)``.
        """
        if not self:
            raise IndexError("pop from an empty path")
        source = self._vertices.popleft()
        edge_label = self._edge_labels.popleft()
        reverse = self._signs.popleft()
        return (source, self.start(), edge_label)

    def is_oriented(self):
        return all(sign == 1 for sign in self._signs)

    def is_closed(self):
        return self.start() == self.end()


class DelaunayStrebelPath(DiGraphPath):
    r"""
    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from surface_dynamics import Stratum
        sage: from veerer.delaunay_strebel_path import DelaunayStrebelPath
        sage: DS = VeeringTriangulation.from_stratum(Stratum([1, 1])).delaunay_strebel_graph()
        sage: start = next(iter(DS))
        sage: path = DelaunayStrebelPath(DS, start)
        sage: path.random_append(10, reverse=False)
        sage: separatrices = [(h, 0) for h in path.start().right_wedges()]
        sage: separatrices_image = [path.vertex_separatrix_transport(h, a) for (h, a) in separatrices]
        sage: separatrices_target = [(h, 0) for h in path.end().right_wedges()]
        sage: assert set(separatrices_image) == set(separatrices_target), (separatrices, separatrices_image, separatrices_target)
    """
    @staticmethod
    def _separatrix_relabelling(relabelling, half_edge, angle):
        return (relabelling[half_edge], angle)

    @staticmethod
    def _separatrix_relabelling_back(relabelling, half_edge, angle):
        return (perm_preimage(relabelling, half_edge), angle)

    # Transport of vertex separatrices (separatrices of a zero of a simple pole of a quadratic differential)

    @staticmethod
    def _vertex_separatrix_flip(state, e, col, half_edge, angle):
        assert half_edge != 2 * e and half_edge != (2 * e + 1)
        a, b, c, d = state.square_about_half_edge(2 * e)
        if half_edge == b:
            assert angle == 0
            return (2 * e + 1, 0) if col == RED else (half_edge, angle)
        elif half_edge == d:
            assert angle == 0
            return (2 * e, 0) if col == RED else (half_edge, angle)

        return (half_edge, angle)

    @staticmethod
    def _vertex_separatrix_flip_back(state, e, col, half_edge, angle):
        if half_edge == 2 * e:
            assert state._colouring[e] == RED
            assert angle == 0
            a, b, c, d = state.square_about_half_edge(2 * e)
            return (c, 0)
        elif half_edge == 2 * e + 1:
            assert state._colouring[e] == RED
            assert angle == 0
            a, b, c, d = state.square_about_half_edge(2 * e)
            return (a, 0)

        return (half_edge, angle)

    @staticmethod
    def _vertex_separatrix_rotate(state, half_edge, angle):
        # blue half-edge: nothing on angle, always fine
        # red half-edge: do -1 on angle, need to explore previous if angle=0
        next_half_edge = state.next_at_vertex(half_edge)
        if state._colouring[half_edge // 2] == RED:
            if angle == 0:
                half_edge = state.previous_at_vertex(half_edge)
                num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                while num_seps == 0:
                    half_edge = state.previous_at_vertex(half_edge)
                    num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                angle = num_seps - 1
            else:
                angle -= 1

        return (half_edge, angle)

    @staticmethod
    def _vertex_separatrix_rotate_back(state, half_edge, angle):
        # blue half-edge: +1 on angle, if next half-edge is blue and angle=max need to explore next
        # red half-edge: nothing on angle, if next half-edge is blue and angle=max need to explore next
        if state._colouring[half_edge // 2] == BLUE:
            angle += 1

        next_half_edge = state.next_at_vertex(half_edge)
        if state._colouring[next_half_edge // 2] == BLUE:
            num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
            if num_seps == angle:
                half_edge = next_half_edge
                num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                while num_seps == 0:
                    half_edge = state.next_at_vertex(half_edge)
                    num_seps = state.half_edge_num_separatrices(half_edge, HORIZONTAL)
                angle = 0

        return (half_edge, angle)

    @staticmethod
    def _vertex_separatrix_strebel(state, mapping, half_edge, angle):
        while mapping[half_edge] == -1:
            half_edge = state.previous_at_vertex(half_edge)
            angle += state._bdry[half_edge] + (state._colouring[half_edge // 2] == RED and state._colouring[state._vp[half_edge] // 2] == BLUE)
        return (mapping[half_edge], angle)

    @staticmethod
    def _vertex_separatrix_strebel_back(state, mapping, half_edge, angle):
        half_edge = next(h for h in range(len(mapping)) if mapping[h] == half_edge)
        num_seps = state._bdry[half_edge] + (state._colouring[half_edge // 2] == RED and state._colouring[state._vp[half_edge] // 2] == BLUE)
        while angle >= num_seps:
            angle -= num_seps
            half_edge = state.next_at_vertex(half_edge)
            num_seps = state._bdry[half_edge] + (state._colouring[half_edge // 2] == RED and state._colouring[state._vp[half_edge] // 2] == BLUE)

        return (half_edge, angle)

    def vertex_separatrix_transport(self, half_edge, angle):
        r"""
        Transport the vertex separatrix ``(half_edge, angle)`` along this path.
        """
        for i in range(len(self)):
            source = self._vertices[i]
            target = self._vertices[i + 1]
            transition = self._edge_labels[i]

            reverse = self._signs[i]
            if reverse:
                source, target = target, source

            # (source, target) follows the orientation of the graph
            assert self._graph.has_edge(source, target, transition)

            if reverse:
                target._check_vertex_separatrix(half_edge, angle)
            else:
                source._check_vertex_separatrix(half_edge, angle)

            kind = transition[0]
            if kind == "flip":
                edges = transition[1]
                old_col = transition[2]
                new_col = transition[3]
                relabelling = transition[4]
                if reverse:
                    for e in edges:
                        half_edge, angle = self._vertex_separatrix_flip_back(target, relabelling[2 * e] // 2, old_col, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling_back(relabelling, half_edge, angle)
                else:
                    for e in edges:
                        half_edge, angle = self._vertex_separatrix_flip(source, e, new_col, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling(relabelling, half_edge, angle)

            elif kind == "rotate":
                relabelling = transition[1]
                if reverse:
                    half_edge, angle = self._vertex_separatrix_rotate_back(target, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling_back(relabelling, half_edge, angle)
                else:
                    half_edge, angle = self._vertex_separatrix_rotate(source, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling(relabelling, half_edge, angle)

            elif kind == "strebel":
                mapping = transition[1]
                if reverse:
                    # NOTE: for Strebel operation the argument is always the veering triangulation
                    half_edge, angle = self._vertex_separatrix_strebel_back(source, mapping, half_edge, angle)
                else:
                    half_edge, angle = self._vertex_separatrix_strebel(source, mapping, half_edge, angle)

            if reverse:
                source._check_vertex_separatrix(half_edge, angle)
            else:
                target._check_vertex_separatrix(half_edge, angle)

        return (half_edge, angle)

    # Transport of face separatrices (separatrices of a higher order poles)

    @staticmethod
    def _face_separatrix_flip(state, e, col, half_edge, angle):
        assert half_edge != 2 * e and half_edge != (2 * e + 1)
        a, b, c, d = state.square_about_half_edge(2 * e)
        if half_edge == b:
            assert angle == 0
            return (2 * e + 1, 0) if col == RED else (half_edge, angle)
        elif half_edge == d:
            assert angle == 0
            return (2 * e, 0) if col == RED else (half_edge, angle)
        else:
            return (half_edge, angle)

    @staticmethod
    def _face_separatrix_flip_back(state, e, col, half_edge, angle):
        if half_edge == 2 * e:
            assert state._colouring[e] == RED
            assert angle == 0
            a, b, c, d = state.square_about_half_edge(2 * e)
            return (c, 0)
        elif half_edge == 2 * e + 1:
            assert state._colouring[e] == RED
            assert angle == 0
            a, b, c, d = state.square_about_half_edge(2 * e)
            return (a, 0)
        else:
            return (half_edge, angle)

    @staticmethod
    def _face_separatrix_rotate(state, half_edge, angle):
        half_edge = state.previous_at_vertex(half_edge)
        while state.half_edge_colour(half_edge) == BLUE:
            half_edge = state.previous_at_vertex(half_edge)
        return (half_edge, angle)

    @staticmethod
    def _face_separatrix_rotate_back(state, half_edge, angle):
        half_edge = state.next_at_vertex(half_edge)
        while state.half_edge_colour(half_edge) == BLUE:
            half_edge = state.next_at_vertex(half_edge)
        return (half_edge, angle)

    @staticmethod
    def _face_separatrix_strebel(state, mapping, half_edge, angle):
        raise NotImplementedError

    @staticmethod
    def _face_separatrix_strebel_back(state, mapping, half_edge, angle):
        raise NotImplementedError

    def face_separatrix_transport(self, half_edge, angle):
        r"""
        Transport the face separatrix ``(half_edge, angle)`` along this path.
        """
        for i in range(len(self)):
            source = self._vertices[i]
            target = self._vertices[i + 1]
            transition = self._edge_labels[i]

            source._check_face_separatrix(half_edge, angle)

            reverse = self._signs[i]
            kind = transition[0]
            if kind == "flip":
                edges = transition[1]
                old_col = transition[2]
                new_col = transition[3]
                relabelling = transition[4]
                if reverse:
                    for e in edges:
                        half_edge, angle = self._face_separatrix_flip_back(target, relabelling[e], old_col, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling_back(relabelling, half_edge, angle)
                else:
                    for e in edges:
                        half_edge, angle = self._face_separatrix_flip(source, e, new_col, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling(relabelling, half_edge, angle)
            elif kind == "rotate":
                relabelling = transition[1]
                if reverse:
                    half_edge, angle = self._face_separatrix_rotate_back(target, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling_back(relabelling, half_edge, angle)
                else:
                    half_edge, angle = self._face_separatrix_rotate(source, half_edge, angle)
                    half_edge, angle = self._separatrix_relabelling(relabelling, half_edge, angle)
            elif kind == "strebel":
                raise NotImplementedError

            target._check_face_separatrix(half_edge, angle)

            return (half_edge, angle)
