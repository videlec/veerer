r"""
Real linear subvarieties in the moduli space of meromorphic Abelian differentials.
"""

from .veering_triangulation import VeeringTriangulation
from .strebel_graph import StrebelGraph

class IrreducibleRealLinearSubvariety:
    def __init__(self, ds_graph):
        self._graph = ds_graph

    def __repr__(self):
        return "Irreducible real linear subvariety of dimension {} in {}".format(
            self.dimension(), self.ambient_stratum())

    def an_element(self):
        r"""
        Return a translation or half-translation surface in this subvariety.
        """

    def ambient_stratum(self):
        return next(iter(self._graph)).stratum()

    def dimension(self):
        return next(iter(self._graph)).dimension()

    def rank(self):
        raise NotImplementedError

    def strebel_delaunay_graph(self):
        return self._graph

    def codimension_one_horizontal_degenerations(self):
        r"""
        Return the list of codimension one horizontal degenerations as a list of Delaunay-Strebel automata.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamilies, DelaunayStrebelAutomaton

        The example of the stratum H(2)::

            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L.codimension_one_horizontal_degenerations()
            [Irreducible real linear subvariety of dimension 3 in H_1(2, -1^2)]

        Degenerations of the eigenform loci of discriminant 17 in the stratum H(1,1). Even though these are
        two distinct linear subvarieties (distinguished by the spin) they have the same number of codimension
        one horizontal degenerations::

            sage: a0, b0, c0, e0 = next(VeeringTriangulationLinearFamilies.H2_prototype_parameters(17, spin=0))
            sage: X17_0 = VeeringTriangulationLinearFamilies.prototype_H2(a0, b0, c0, e0)
            sage: L0 = X17_0.linear_subvariety()  # long time ~5secs
            sage: L0.codimension_one_horizontal_degenerations()  # long time
            [Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2)]

            sage: a1, b1, c1, e1 = next(VeeringTriangulationLinearFamilies.H2_prototype_parameters(17, spin=1))
            sage: X17_1 = VeeringTriangulationLinearFamilies.prototype_H2(a1, b1, c1, e1)
            sage: L1 = X17_1.linear_subvariety()  # long time ~5secs
            sage: L1.codimension_one_horizontal_degenerations()  # long time
            [Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2)]
        """
        degenerations = set()
        automata = []
        for state in self.strebel_delaunay_graph():
            if isinstance(state, VeeringTriangulation):
                for (f_up, f_low) in state.codimension_one_horizontal_degenerations(mutable=True):
                    assert f_up is None
                    assert f_low.dimension() == state.dimension() - 1
                    f_low.set_canonical_labels()
                    f_low.set_immutable()
                    degenerations.add(f_low)

        # NOTE: since we have the full list of Delaunay cells, we do not need to run
        # the expensive Strebel -> Delaunay
        from .automaton import DelaunayStrebelAutomaton
        DS = DelaunayStrebelAutomaton(backward=False)
        for state in degenerations:
            DS.add_seed(state, setup=False)
        DS.run()

        assert set(state for state in DS if isinstance(state, VeeringTriangulation)) == degenerations

        return [IrreducibleRealLinearSubvariety(graph) for graph in DS._graph.connected_components_subgraphs()]
