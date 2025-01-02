r"""
Paths in Delaunay-Strebel graph and monodromy of linear subvarieties.
"""

from collections import deque

from sage.misc.prandom import choice, randrange

from veerer.constants import BLUE, RED
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
        Closed path of length 4 in 5-dimensional Butterfly from ('11000', 0) to ('11000', 0)
    """
    def __init__(self, graph, start):
        self._graph = graph
        self._vertices = deque([start])  # vertices
        self._edge_labels = deque([])    # edge labels
        self._signs = deque([])          # 1 if edge is taken backward

    def __bool__(self):
        return bool(self._edge_labels)

    def __len__(self):
        return len(self._edge_labels)

    def __repr__(self):
        return "{} of length {} in {} from {} to {}".format("Closed path" if self.is_closed() else "Path", len(self), self._graph, self.start(), self.end())

    def start(self):
        return self._vertices[0]

    def end(self):
        return self._vertices[-1]

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
    def _vertex_separatrix_flip(source, target, e, col, sep_half_edge, sep_angle):
        assert sep_half_edge != 2 * e and sep_half_edge != (2 * e + 1)
        a, b, c, d = source.square_about_half_edge(2 * e)
        if sep_half_edge == b:
            assert sep_angle == 0
            return (2 * e + 1, 0) if col == RED else (sep_half_edge, sep_angle)
        elif sep_half_edge == d:
            assert sep_angle == 0
            return (2 * e, 0) if col == RED else (sep_half_edge, sep_angle)
        else:
            return (sep_half_edge, sep_angle)

    @staticmethod
    def _vertex_separatrix_flip_back(source, target, e, col, sep_half_edge, sep_angle):
        if sep_half_edge == 2 * e:
            assert source._colouring[e] == RED
            assert sep_angle == 0
            a, b, c, d = source.square_about_half_edge(2 * e)
            return (c, 0)
        elif sep_half_edge == 2 * e + 1:
            assert source._colouring[e] == RED
            assert sep_angle == 0
            a, b, c, d = source.square_about_half_edge(2 * e)
            return (a, 0)
        else:
            return (sep_half_edge, sep_angle)

    @staticmethod
    def _vertex_separatrix_rotate(source, target):
        sep_half_edge = source.previous_at_vertex(sep_half_edge)
        while source.half_edge_colour(sep_half_edge) == BLUE:
            sep_half_edge = source.previous_at_vertex(sep_half_edge)
        sep_half_edge, sep_angle = (sep_half_edge, 0)
        return (sep_half_edge, sep_angle)

    @staticmethod
    def _vertex_separatrix_rotate_back(source, target):
        sep_half_edge = source.next_at_vertex(sep_half_edge)
        while source.half_edge_colour(sep_half_edge) == BLUE:
            sep_half_edge = source.next_at_vertex(sep_half_edge)
        return (sep_half_edge, 0)

    @staticmethod
    def _vertex_separatrix_relabelling(source, target, relabelling, sep_half_edge, sep_angle):
        return (relabelling[sep_half_edge], sep_angle)

    @staticmethod
    def _vertex_separatrix_relabelling_back(source, target, relabelling, sep_half_edge, sep_angle):
        raise (perm_preimage(relabelling, sep_half_edge), sep_angle)

    def vertex_separatrix_transport(self, half_edge, angle):
        for i in range(len(self)):
            source = self._vertices[i]
            target = self._vertices[i + 1]
            transition = self._edge_labels[i]

            source._check_separatrix(half_edge, angle)

            reverse = self._signs[i]
            kind = transition[0]
            if kind == "flip":
                edges = transition[1]
                old_col = transition[2]
                new_col = transition[3]
                relabelling = transition[4]
                if reverse:
                    for e in edges:
                        half_edge, angle = self._vertex_separatrix_flip_back(target, source, relabelling[e], old_col, half_edge, angle)
                    half_edge, angle = self._vertex_separatrix_relabelling_back(target, source, relabelling, half_edge, angle)
                else:
                    for e in edges:
                        half_edge, angle = self._vertex_separatrix_flip(source, target, e, new_col, half_edge, angle)
                    half_edge, angle = self._vertex_separatrix_relabelling(source, target, relabelling, half_edge, angle)
            elif kind == "rotate":
                raise NotImplementedError
            elif kind == "strebel":
                raise NotImplementedError

            target._check_separatrix(half_edge, angle)
            return (half_edge, angle)

    @staticmethod
    def _face_separatrix_flip(source, target, e, col, sep_half_edge, sep_angle):
        raise NotImplementedError

    @staticmethod
    def _face_separatrix_flip_back(source, target, e, col, sep_half_edge, sep_angle):
        raise NotImplementedError

    @staticmethod
    def _face_separatrix_rotate(source, target):
        raise NotImplementedError

    @staticmethod
    def _face_separatrix_rotate_back(source, target):
        raise NotImplementedError

    @staticmethod
    def _face_separatrix_relabelling(source, target, relabelling, sep_half_edge, sep_angle):
        raise NotImplementedError

    @staticmethod
    def _face_separatrix_relabelling_back(source, target, relabelling, sep_half_edge, sep_angle):
        raise NotImplementedError

    def face_separatrix_transport(self, half_edge, angle):
        source = self._vertices[i]
        target = self._vertices[i + 1]
        transition = self._edge_labels[i]

        source._check_separatrix(half_edge, angle)

        reverse = self._signs[i]
        kind = transition[0]
        if kind == "flip":
            edges = transition[1]
            old_col = transition[2]
            new_col = transition[3]
            relabelling = transition[4]
            if reverse:
                for e in edges:
                    half_edge, angle = self._vertex_separatrix_flip_back(target, source, relabelling[e], old_col, half_edge, angle)
                half_edge, angle = self._vertex_separatrix_relabelling_back(target, source, relabelling, half_edge, angle)
            else:
                for e in edges:
                    half_edge, angle = self._vertex_separatrix_flip(source, target, e, new_col, half_edge, angle)
                half_edge, angle = self._vertex_separatrix_relabelling(source, target, relabelling, half_edge, angle)
        elif kind == "rotate":
            raise NotImplementedError
        elif kind == "strebel":
            raise NotImplementedError

        return half_edge, angle


