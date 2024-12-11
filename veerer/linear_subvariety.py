r"""
Real linear subvarieties in the moduli space of meromorphic Abelian differentials.
"""

import itertools
import numbers

from .automaton import DelaunayStrebelAutomaton
from .veering_triangulation import VeeringTriangulation
from .strebel_graph import StrebelGraph

from sage.misc.cachefunc import cached_method
from sage.graphs.digraph import DiGraph

class IrreducibleRealLinearSubvariety:
    def __init__(self, ds_graphs):
        if isinstance(ds_graphs, (tuple, list)):
            self._levels = tuple(ds_graphs)
        elif isinstance(ds_graphs, DiGraph):
            self._levels = (ds_graphs,)
        else:
            raise TypeError("got {}".format(type(ds_graphs).__name__))

    @cached_method
    def _min(self):
        return tuple(min(state for state in ds_graph if isinstance(state, VeeringTriangulation)) for ds_graph in self._levels)

    def __eq__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return self._min() == other._min()

    def __ne__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return self._min() != other._min()

    def __lt__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return self._min() < other._min()

    def __le__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return self._min() <= other._min()

    def __gt__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return self._min() > other._min()

    def __ge__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return self._min() >= other._min()

    def _check_level(self, level):
        if not isinstance(level, numbers.Integral):
            raise TypeError("level must be integral")
        level = int(level)
        if level < 0:
            level = -level
        if not 0 <= level < len(self._levels):
            raise ValueError("level out of range")
        return level

    def __repr__(self):
        return "Irreducible real linear subvariety of projective dimension {} in {}".format(
            self.projective_dimension(), self.ambient_stratum())

    def levels(self):
        return range(len(self._levels))

    def an_element(self):
        r"""
        Return a translation or half-translation surface in this subvariety.
        """

    def ambient_stratum(self, level=None):
        if level is None:
            return [self.ambient_stratum(level) for level in self.levels()]
        level = self._check_level(level)
        return next(iter(self._levels[level])).stratum()

    def dimension(self, level=None):
        r"""
        Return the unprojectivized dimension.
        """
        if level is None:
            return sum(self.dimension(level) for level in self.levels())
        level = self._check_level(level)
        return next(iter(self._levels[level])).dimension()

    def projective_dimension(self, level=None):
        if level is None:
            return self.dimension() - len(self._levels)
        else:
            level = self._check_level(level)
            return self.dimension(level) - 1

    def rank(self):
        raise NotImplementedError

    def strebel_delaunay_graph(self, level):
        level = self._check_level(level)
        return self._levels[level]

    def codimension_one_horizontal_degenerations(self, level=None):
        r"""
        Return the list of codimension one horizontal degenerations as a list of Delaunay-Strebel automata.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamilies, DelaunayStrebelAutomaton

        The example of the stratum H(2)::

            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L.dimension()
            4
            sage: L.codimension_one_horizontal_degenerations()  # optional - surface_dynamics
            [Irreducible real linear subvariety of projective dimension 2 in [H_1(2, -1^2)]]

        Degenerations of the eigenform loci of discriminant 17 in the stratum H(1,1). Even though these are
        two distinct linear subvarieties (distinguished by the spin) they have the same number of codimension
        one horizontal degenerations::

            sage: a0, b0, c0, e0 = next(VeeringTriangulationLinearFamilies.H2_prototype_parameters(17, spin=0))
            sage: X17_0 = VeeringTriangulationLinearFamilies.prototype_H2(a0, b0, c0, e0)
            sage: L0 = X17_0.linear_subvariety()  # long time ~5secs
            sage: L0.codimension_one_horizontal_degenerations()  # long time # optional - surface_dynamics
            [Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2)]

            sage: a1, b1, c1, e1 = next(VeeringTriangulationLinearFamilies.H2_prototype_parameters(17, spin=1))
            sage: X17_1 = VeeringTriangulationLinearFamilies.prototype_H2(a1, b1, c1, e1)
            sage: L1 = X17_1.linear_subvariety()  # long time ~5secs
            sage: L1.codimension_one_horizontal_degenerations()  # long time # optional - surface_dynamics
            [Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2)]
        """
        if level is None:
            return [degeneration for level in self.levels() for degeneration in self.codimension_one_horizontal_degenerations(level)]

        level = self._check_level(level)
        degenerations = set()
        automata = []
        for state in self.strebel_delaunay_graph(level):
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

    # TODO: we do NOT get codimension one things with this method...
    def codimension_one_vertical_degenerations(self, level=None):
        r"""
        Return the list of codiemsnion one vertical degenerations as a list of Delauany-Strebel automata.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L # optional - surface_dynamics
            Irreducible real linear subvariety of projective dimension 3 in [H_2(2)]
            sage: deg_first = sorted(L.codimension_one_vertical_degenerations()) # optional - surface_dynamics
            sage: deg_first # optional - surface_dynamics
            [Irreducible real linear subvariety of projective dimension 2 in [H_1(0), H_1(2, -2)],
             Irreducible real linear subvariety of projective dimension 2 in [H_1(0^2), H_0(2, -2^2)]]
            sage: deg_second = sorted(set(L2 for L1 in deg_first for L2 in L1.codimension_one_vertical_degenerations())) # optional - surface_dynamics
            sage: deg_second # optional - surface_dynamics
        """
        if level is None:
            return [degeneration for level in self.levels() for degeneration in self.codimension_one_vertical_degenerations(level)]

        level = self._check_level(level)
        degenerations = set()
        automata = []
        for state in self.strebel_delaunay_graph(level):
            if isinstance(state, VeeringTriangulation):
                for (f_up, f_low) in state.codimension_one_vertical_degenerations(mutable=True):
                    assert f_up is not None
                    # NOTE: the projectivization makes us loose one dimension
                    assert f_low.dimension() + f_up.dimension() == state.dimension()
                    assert f_low.is_delaunay()
                    assert f_up.is_delaunay()
                    f_up.set_canonical_labels()
                    f_up.set_immutable()
                    f_low.set_canonical_labels()
                    f_low.set_immutable()
                    degenerations.add((f_up, f_low))

        # NOTE: since we have the full list of Delaunay cells, we do not need to run
        # the expensive Strebel -> Delaunay
        from .automaton import DelaunayStrebelAutomaton
        DS_up = DelaunayStrebelAutomaton(backward=False)
        for f_up, f_low in degenerations:
            DS_up.add_seed(f_up, setup=False)
        DS_up.run()

        DS_low = DelaunayStrebelAutomaton(backward=False)
        for f_up, f_low in degenerations:
            DS_low.add_seed(f_low, setup=False)
        DS_low.run()

        assert set(state for state in DS_up if isinstance(state, VeeringTriangulation)) == set(f_up for f_up, f_low in degenerations)
        assert set(state for state in DS_low if isinstance(state, VeeringTriangulation)) == set(f_low for f_up, f_low in degenerations)

        # retrieve which pairs of Delaunay-Strebel graph corresponds to actual
        # pairs (f_up, f_low)
        ccs_up = DS_up._graph.connected_components_subgraphs()
        ccs_low = DS_low._graph.connected_components_subgraphs()
        pairs = set()
        for (f_up, f_low) in degenerations:
            i_up = next(j for j, cc in enumerate(ccs_up) if f_up in cc)
            i_low = next(j for j, cc in enumerate(ccs_low) if f_low in cc)
            pairs.add((i_up, i_low))

        ans = []
        for (i_up, i_low) in pairs:
            ds_up = ccs_up[i_up]
            ds_low = ccs_low[i_low]
            new_levels = self._levels[:level] + (ds_up, ds_low) + self._levels[level + 1:]
            ans.append(IrreducibleRealLinearSubvariety(new_levels))
        return ans
