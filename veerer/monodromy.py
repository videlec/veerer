from sage.graphs.digraph import DiGraph
from sage.groups.perm_gps.permgroup_named import SymmetricGroup

from .delaunay_strebel_path import DiGraphPath, DelaunayStrebelPath


def digraph_spanning_tree(G, root):
    r"""
    Return a pair ``(tree, complementary_edges)`` that form a spanning
    tree of ``G``.

    The edges in the tree are directed towards the ``root`` vertex.  The edge
    labels are pairs ``(edge_label, reverse)`` where reverse is ``0`` if the
    direction of the edge in ``G`` and the tree coincide and ``1`` otherwise.
    """
    # oriented towards the root
    # make a spanning tree
    T = DiGraph(loops=False, multiedges=False)
    T.add_vertex(root)
    complementary_edges = []
    todo = [root]
    while todo:
        u = todo.pop()
        for (v, _, edge_label) in G.incoming_edges(u):
            if v not in T:
                T.add_edge((v, u, (edge_label, 0)))
                todo.append(v)
            else:
                complementary_edges.append((v, u, edge_label))
        for (_, v, edge_label) in G.outgoing_edges(u):
            if v not in T:
                T.add_edge((v, u, (edge_label, 1)))
                todo.append(v)

    return T, complementary_edges


def graph_fundamental_group_basis(G, root, path_class=DiGraphPath):
    r"""
    Iterate through a basis of the fundamental group of the digraph ``G``.

    EXAMPLES::

        sage: from veerer.monodromy import graph_fundamental_group_basis
        sage: G = digraphs.DeBruijn(2, 3)
        sage: for path in graph_fundamental_group_basis(G, '000'):
        ....:     print(path)
        Closed path of length 1 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 2 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 3 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 4 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 6 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 7 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 6 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 7 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 6 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 7 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 4 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 6 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 4 in De Bruijn digraph (k=2, n=3) at 000
        Closed path of length 5 in De Bruijn digraph (k=2, n=3) at 000
    """
    T, complementary_edges = digraph_spanning_tree(G, root)
    for source, target, transition in complementary_edges:
        path = path_class(G, source)
        path.append(target, transition)

        while path.start() != root:
            edges = T.outgoing_edges(path.start())
            assert len(edges) == 1
            u, v, (transition, sign) = edges[0]
            if sign:
                assert G.has_edge(v, u, transition)
                path.appendleft(v, transition, reverse=False)
            else:
                assert G.has_edge(u, v, transition)
                path.appendleft(v, transition, reverse=True)

        while path.end() != root:
            edges = T.outgoing_edges(path.end())
            assert len(edges) == 1
            u, v, (transition, sign) = edges[0]
            if sign:
                assert G.has_edge(v, u, transition)
                path.append(v, transition, reverse=True)
            else:
                assert G.has_edge(u, v, transition)
                path.append(v, transition, reverse=False)

        yield path


# TODO: this function has to move closer to Delaunay-Strebel graphs and linear subvarieties
def vertex_separatrices_monodromy(ds_graph, root=None):
    r"""
    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from veerer.monodromy import vertex_separatrices_monodromy

    The case of H(1,1)::

        sage: vt = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,9)(~8,10,11)(~9,~10,~11)", "BRBBRBBRBBRB")
        sage: ds_graph = vt.delaunay_strebel_graph()
        sage: assert vt in ds_graph  # we pick a veering triangulation in canonical form
        sage: G = vertex_separatrices_monodromy(ds_graph, vt)
        sage: G.cardinality()
        8
        sage: G.structure_description()
        'C4 x C2'
    """
    if root is None:
        root = next(state for state in DS if isinstance(state, VeeringTriangulation))

    separatrix_vertex_angle = {}
    separatrix_index = {}
    separatrices = []
    i = 0
    for v, seps in enumerate(root.vertex_separatrices(flat=False)):
        for a, s in enumerate(seps):
            separatrix_vertex_angle[s] = (v, a)
            separatrix_index[s] = i
            separatrices.append(s)
            i += 1

    perms = set(tuple(separatrix_index[path.vertex_separatrix_transport(h, a)] for (h, a) in separatrices)
               for path in graph_fundamental_group_basis(ds_graph, root, DelaunayStrebelPath))
    S = SymmetricGroup(range(len(separatrices)))
    return S.subgroup([S(list(p)) for p in perms])
