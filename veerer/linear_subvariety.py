r"""
Real linear subvarieties in the moduli space of meromorphic Abelian differentials.
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024 Vincent Delecroix
#                     2024 Kai Fu
#
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License
#  as published by the Free Software Foundation; either version 2
#  of the License, or (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
# ****************************************************************************

import collections
import itertools
import numbers
import sys

from .automaton import DelaunayStrebelAutomaton
from .veering_triangulation import VeeringTriangulation
from .strebel_graph import StrebelGraph

from sage.structure.richcmp import op_LT, op_LE, op_EQ, op_NE, op_GT, op_GE, rich_to_bool
from sage.misc.cachefunc import cached_method
from sage.graphs.digraph import DiGraph


# TODO: vertical/horizontal degenerations commute
class Degenerations:
    r"""
    Helper class for computing successive degenerations of (primitive) linear subvarieties.
    """
    def __init__(self):
        self._to_components = {}  # veering triangulation/strebel graph -> component number
        self._components = []     # list of connected subgraphs
        self._mins = []           # the minimum of each component
        self._horizontal_degenerations = [] # each element is a list of tuples representing a list of single level subvarieties
        self._vertical_degenerations = [] # each element is a list of pairs of tuples representing a list of bi-level primitive

    def __repr__(self):
        return "Degenerations of {} veering triangulations or Strebel graphs into {} prime components".format(len(self._to_components), len(self._components))

    def _check_component_number(self, component_number):
        if not isinstance(component_number, numbers.Integral):
            raise TypeError("component_number must be an integer")
        component_number = int(component_number)
        if component_number < 0 or component_number >= len(self._components):
            raise ValueError("component_number (={}) must a positive integer smaller than {}".format(len(self._components)))
        return component_number

    def find(self, g):
        r"""
        Find the Delaunay-Strebel graph ``g`` in the already computed list or
        add it to the list and return the associated index.
        """
        vt = next(state for state in g if isinstance(state, VeeringTriangulation))
        if not vt.is_prime():
            raise ValueError("not-prime")
        if vt in self._to_components:
            return self._to_components[vt]
        else:
            return self.add(g)

    def add(self, g):
        vt_min = next(state for state in g if isinstance(state, VeeringTriangulation))
        num = len(self._components)
        self._components.append(g)
        self._mins.append(vt_min)
        self._horizontal_degenerations.append(None)
        self._vertical_degenerations.append(None)
        for state in g:
            self._to_components[state] = num
        return num

    def pending_vertical_degenerations(self):
        r"""
        Return the list of component indices whose list of vertical degenerations is still unknown.
        """
        return [i for i, degenerations in enumerate(self._vertical_degenerations) if degenerations is None]

    def pending_horizontal_degenerations(self):
        r"""
        Return the list of component indices whose list of horizontal degenerations is still unknown.
        """
        return [i for i, degenerations in enumerate(self._horizontal_degenerations) if degenerations is None]

    def find_and_decompose(self, f):
        r"""
        Given a linear family ``f`` decompose it into prime components and
        return a pair ``(known_prime_component_indices, unknown_prime_components)``
        """
        if f.is_prime():
            f.set_canonical_labels()
            f.set_immutable()
            if f in self._to_components:
                component_number = self._to_components[f]
                return (component_number,), ()
            else:
                return (), (f,)
        else:
            prime_components = [comp for atom, comp in f.prime_decomposition(mutable=True, check=True)]
            if f.is_abelian() and not all(ff.is_abelian() for ff in prime_components):
                raise ValueError("{}\n{}".format(f, prime_components))
            prime_components_known = []
            prime_components_unknown = []
            for ff in prime_components:
                ff.set_canonical_labels()
                ff.set_immutable()
                if ff in self._to_components:
                    component_number = self._to_components[ff]
                    prime_components_known.append(component_number)
                else:
                    prime_components_unknown.append(ff)
            prime_components_known.sort()
            prime_components_unknown.sort()
            return prime_components_known, prime_components_unknown

    def compute_horizontal_degenerations(self, component_number):
        r"""
        Compute the horizontal degenerations of ``component_number``.
        """
        component_number = self._check_component_number(component_number)
        if self._horizontal_degenerations[component_number] is not None:
            return

        degenerations = set()
        degenerations_prime_components = set()
        ds_graph = self._components[component_number]
        for state in ds_graph:
            if isinstance(state, VeeringTriangulation):
                for (f_up, f_low) in state.codimension_one_horizontal_degenerations(mutable=True, check=False):
                    assert f_up is None
                    assert f_low.dimension() == state.dimension() - 1
                    known, unknown = self.find_and_decompose(f_low)
                    degenerations.add(tuple(known + unknown))
                    degenerations_prime_components.update(unknown)

        # NOTE: since we have the full list of Delaunay cells, we do not need to run
        # the expensive Strebel -> Delaunay (ie we can set backward=False in the
        # construction of the automata below).
        from .automaton import DelaunayStrebelAutomaton
        ds_graph = DelaunayStrebelAutomaton(backward=False)
        for state in degenerations_prime_components:
            ds_graph.add_seed(state, setup=False)
        ds_graph.run()
        assert set(state for state in ds_graph if isinstance(state, VeeringTriangulation)) == degenerations_prime_components

        for g in ds_graph._graph.connected_components_subgraphs():
            self.add(g)

        ans = self._horizontal_degenerations[component_number] = set()
        for f in degenerations:
            degeneration = tuple(sorted(x if isinstance(x, int) else self._to_components[x] for x in f))
            ans.add(degeneration)

    def compute_vertical_degenerations(self, component_number):
        component_number = self._check_component_number(component_number)
        if self._vertical_degenerations[component_number] is not None:
            return

        degenerations = set()
        degenerations_prime_components = set()
        ds_graph = self._components[component_number]
        for state in ds_graph:
            if isinstance(state, VeeringTriangulation):
                for (f_up, f_low) in state.codimension_one_vertical_degenerations(mutable=True, check=False):
                    assert f_up is not None, (state,)
                    # NOTE: the projectivization makes us loose one dimension
                    assert f_low.dimension() + f_up.dimension() == state.dimension()
                    # too long assert f_low.is_delaunay()
                    # too long assert f_up.is_delaunay()

                    known_up, unknown_up = self.find_and_decompose(f_up)
                    f_up_decomposed = tuple(known_up + unknown_up)
                    degenerations_prime_components.update(unknown_up)
                    known_low, unknown_low = self.find_and_decompose(f_low)
                    f_low_decomposed = tuple(known_low + unknown_low)
                    degenerations_prime_components.update(unknown_low)
                    degenerations.add((f_up_decomposed, f_low_decomposed))

        # NOTE: since we have the full list of Delaunay cells, we do not need to run
        # the expensive Strebel -> Delaunay
        from .automaton import DelaunayStrebelAutomaton
        ds_graph = DelaunayStrebelAutomaton(backward=False)
        for state in degenerations_prime_components:
            ds_graph.add_seed(state, setup=False)
        ds_graph.run()
        assert set(state for state in ds_graph if isinstance(state, VeeringTriangulation)) == degenerations_prime_components

        for g in ds_graph._graph.connected_components_subgraphs():
            self.add(g)

        ans = self._vertical_degenerations[component_number] = set()
        for f_up, f_low in degenerations:
            degeneration_up = tuple(sorted(x if isinstance(x, int) else self._to_components[x] for x in f_up))
            degeneration_low = tuple(sorted(x if isinstance(x, int) else self._to_components[x] for x in f_low))
            ans.add((degeneration_up, degeneration_low))

    def compute_all(self):
        vpending = self.pending_vertical_degenerations()
        hpending = self.pending_horizontal_degenerations()
        while vpending or hpending:
            for i in vpending:
                self.compute_vertical_degenerations(i)
            for i in hpending:
                self.compute_horizontal_degenerations(i)
            vpending = self.pending_vertical_degenerations()
            hpending = self.pending_horizontal_degenerations()

    def codimension_one_vertical_degenerations(self, g):
        r"""
        Return the codimension one vertical degenerations of the Delaunay-Strebel graph ``g``.
        """
        component_number = self.find(g)
        self.compute_vertical_degenerations(component_number)
        ans = []
        for up, low in self._vertical_degenerations[component_number]:
            ans.append((tuple(self._components[i] for i in up), tuple(self._components[i] for i in low)))
        return ans

    def codimension_one_horizontal_degenerations(self, g):
        r"""
        Return the codimension one horizontal degenerations of the Delaunay-Strebel graph ``g``.
        """
        component_number = self.find(g)
        self.compute_horizontal_degenerations(component_number)
        ans = []
        for degeneration in self._horizontal_degenerations[component_number]:
            ans.append(tuple(self._components[i] for i in degeneration))
        return ans


class IrreducibleRealLinearSubvariety:
    r"""
    Irreducible real linear subvariety of the moduli space of multiscale
    Abelian or quadratic differentials.

    Note that each level is decomposed into prime components.

    TESTS::

        sage: from veerer import *
        sage: vt = VeeringTriangulation("(1,2,3)(~1,~2,~3)(0:1)(~0:1)", "BRBB")
        sage: L = vt.linear_subvariety()
        sage: L  # optional - surface_dynamics
        Irreducible real linear subvariety of projective dimension 1 in [[H_0(0, -1^2)], [H_1(0)]]
        sage: L.codimension_one_horizontal_degenerations()  # optional - surface_dynamics
        [Irreducible real linear subvariety of projective dimension 0 in [[H_0(0, -1^2)], [H_0(0, -1^2)]]]
        sage: L.codimension_one_vertical_degenerations()
        []

        sage: vt = VeeringTriangulationLinearFamily("(0:2,1:2)(~0:2,~1:2)", "RR", [(1, 1)])
        sage: M = vt.linear_subvariety().multiscale_compactification()
        sage: M # optional - surface_dynamics
        MultiscaleCompactification Irreducible real linear subvariety of projective dimension 0 in [[H_0(1^2, -2^2)]]
    """
    def __init__(self, ds_graphs):
        if isinstance(ds_graphs, DiGraph):
            ds_graphs = [[ds_graphs]]
        elif isinstance(ds_graphs, (tuple, list)):
            ds_graphs_new = []
            for elt in ds_graphs:
                if isinstance(elt, DiGraph):
                    ds_graphs_new.append([elt])
                elif isinstance(elt, (tuple, list)):
                    ds_graphs_new.append(list(elt))
                else:
                    raise ValueError("invalid input")
            ds_graphs = ds_graphs_new

        # NOTE: in order to normalize we sort the components of each level according
        # to the minima
        levels = list(map(list, ds_graphs))
        mins = []
        for j, level in enumerate(levels):
            level_mins = [(min(state for state in comp if isinstance(state, VeeringTriangulation)), i) for i, comp in enumerate(level)]
            level_mins.sort()
            levels[j] = [level[k] for _, k in level_mins]
            mins.extend(level_mins)

        self._levels = tuple(map(tuple, levels))
        self._mins = tuple(mins)

    def _check(self, error=RuntimeError):
        if not isinstance(self._levels, tuple) or not all(isinstance(level, tuple) for level in self._levels):
            raise error
        if len(self._mins) != sum(map(len, self._levels)):
            raise error
        if not all(x.is_prime() for x in self._mins):
            raise error("all component of a level must be prime; call prime_decomposition first")

    def __hash__(self):
        return hash(self._mins)

    def __eq__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return list(map(len, self._levels)) == list(map(len, other._levels)) and self._mins == other._mins

    def __ne__(self, other):
        if type(self) is not type(other):
            raise TypeError
        return list(map(len, self._levels)) != list(map(len, other._levels)) or self._mins != other._mins

    def _cmp_(self, other):
        if type(self) is not type(other):
            raise TypeError("can not compare {} with {}".format(type(self).__name__, type(other).__name__))

        if type(self) is not type(other):
            raise TypeError
        data0 = len(self._levels)
        data1 = len(other._levels)
        c = (data0 > data1) - (data0 < data1)
        if c:
            return c

        data0 = list(map(len, self._levels))
        data1 = list(map(len, other._levels))
        c = (data0 > data1) - (data0 < data1)
        if c:
            return c

        data0 = self._mins
        data1 = other._mins
        c = (data0 > data1) - (data0 < data1)
        return c

    def _richcmp_(self, other, op):
        if type(self) is not type(other):
            raise TypeError("can not compare {} with {}".format(type(self).__name__, type(other).__name__))

        return rich_to_bool(op, self._cmp_(other))

    def __lt__(self, other):
        return self._richcmp_(other, op_LT)

    def __le__(self, other):
        return self._richcmp_(other, op_LE)

    def __gt__(self, other):
        return self._richcmp_(other, op_GT)

    def __ge__(self, other):
        return self._richcmp_(other, op_GE)

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

    def num_levels(self):
        r"""
        Return the number of levels.
        """
        return len(self._levels)

    def levels(self):
        r"""
        Return the set of levels
        """
        return range(len(self._levels))

    def an_element(self):
        r"""
        Return a translation or half-translation surface in this subvariety.
        """
        raise NotImplementedError

    def signature(self, level=None):
        r"""
        Return the signature (ie order of zeros).

        If level is provided, return a list of degrees. Otherwise, return a
        list of lists.
        """
        if level is None:
            return tuple(self.signature(level) for level in self.levels())
        level = self._check_level(level)
        return tuple(sorted(sum((next(iter(comp)).stratum().signature() for comp in self._levels[level]), tuple())))

    def ambient_stratum(self, level=None):
        r"""
        Return the ambient stratum of this subvariety.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L.ambient_stratum()
            [[H_2(2)]]
            sage: for Ldeg in sorted(L.codimension_one_vertical_degenerations()):
            ....:     print(Ldeg.ambient_stratum())
            [[H_1(0)], [H_1(2, -2)]]
            [[H_1(0^2)], [H_0(2, -2^2)]]
        """
        if level is None:
            return [self.ambient_stratum(level) for level in self.levels()]
        level = self._check_level(level)
        return [next(iter(comp)).stratum() for comp in self._levels[level]]

    def dimension(self, level=None):
        r"""
        Return the ambient stratum of this subvariety.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L.dimension()
            4
            sage: for Ldeg in L.codimension_one_vertical_degenerations():
            ....:     print(Ldeg.dimension())
            4
            4
        """
        if level is None:
            return sum(self.dimension(level) for level in self.levels())
        level = self._check_level(level)
        return sum(next(iter(comp)).dimension() for comp in self._levels[level])

    def projective_dimension(self, level=None):
        r"""
        Return the projective dimension.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L.projective_dimension()
            3
            sage: for Ldeg in L.codimension_one_vertical_degenerations():
            ....:     print(Ldeg.projective_dimension())
            2
            2
        """
        if level is None:
            return self.dimension() - len(self._levels)
        else:
            level = self._check_level(level)
            return self.dimension(level) - 1

    def rank(self):
        raise NotImplementedError

    def delaunay_strebel_graph(self, level):
        level = self._check_level(level)
        return self._levels[level]

    def codimension_one_horizontal_degenerations(self, level=None, degeneration_helper=None):
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
            [Irreducible real linear subvariety of projective dimension 2 in [[H_1(2, -1^2)]]]

        Degenerations of the eigenform loci of discriminant 17 in the stratum H(1,1). Even though these are
        two distinct linear subvarieties (distinguished by the spin) they have the same number of codimension
        one horizontal degenerations::

            sage: a0, b0, c0, e0 = next(VeeringTriangulationLinearFamilies.H2_prototype_parameters(17, spin=0))
            sage: X17_0 = VeeringTriangulationLinearFamilies.prototype_H2(a0, b0, c0, e0)
            sage: L0 = X17_0.linear_subvariety()  # long time ~5secs # not tested
            sage: L0.codimension_one_horizontal_degenerations()  # long time # optional - surface_dynamics # not tested
            [Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2)]

            sage: a1, b1, c1, e1 = next(VeeringTriangulationLinearFamilies.H2_prototype_parameters(17, spin=1))
            sage: X17_1 = VeeringTriangulationLinearFamilies.prototype_H2(a1, b1, c1, e1)
            sage: L1 = X17_1.linear_subvariety()  # long time ~5secs # not tested
            sage: L1.codimension_one_horizontal_degenerations()  # long time # optional - surface_dynamics # not tested
            [Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2),
             Irreducible real linear subvariety of dimension 1 in Q_0(1, -1, -2^2)]
        """
        if level is None:
            return [degeneration for level in self.levels() for degeneration in self.codimension_one_horizontal_degenerations(level, degeneration_helper)]

        level = self._check_level(level)

        if degeneration_helper is None:
            degeneration_helper = Degenerations()

        ans = []
        ds_graphs = self.delaunay_strebel_graph(level)
        for ds_graph_num, ds_graph in enumerate(ds_graphs):
            for ds_degeneration in degeneration_helper.codimension_one_horizontal_degenerations(ds_graph):
                new_level = ds_graphs[:ds_graph_num] + ds_degeneration + ds_graphs[ds_graph_num + 1:]
                new_levels = self._levels[:level] + (new_level,) + self._levels[level + 1:]
                new_subvariety = IrreducibleRealLinearSubvariety(new_levels)
                assert new_subvariety.projective_dimension() == self.projective_dimension() - 1
                assert new_subvariety.num_levels() == self.num_levels()
                ans.append(new_subvariety)
            return ans

    def codimension_one_vertical_degenerations(self, level=None, degeneration_helper=None):
        r"""
        Return the list of codiemsnion one vertical degenerations as a list of Delauany-Strebel automata.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L # optional - surface_dynamics
            Irreducible real linear subvariety of projective dimension 3 in [[H_2(2)]]
            sage: deg_first = sorted(L.codimension_one_vertical_degenerations()) # optional - surface_dynamics
            sage: deg_first # optional - surface_dynamics
            [Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0^2)], [H_0(2, -2^2)]]]
            sage: deg_second = []
            sage: for L1 in deg_first: # optional - surface_dynamics
            ....:     degs = sorted(L1.codimension_one_vertical_degenerations())
            ....:     print(L1, degs)
            ....:     deg_second.extend(degs)
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0^2)], [H_0(2, -2^2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            sage: for L2 in deg_second: # optional - surface_dynamics
            ....:     assert not list(L2.codimension_one_vertical_degenerations())
        """
        if level is None:
            return [degeneration for level in self.levels() for degeneration in self.codimension_one_vertical_degenerations(level, degeneration_helper)]

        level = self._check_level(level)

        if degeneration_helper is None:
            degeneration_helper = Degenerations()

        ds_graphs = self.delaunay_strebel_graph(level)
        ans = []
        for ds_graph_num, ds_graph in enumerate(ds_graphs):
            for (ds_up, ds_low) in degeneration_helper.codimension_one_vertical_degenerations(ds_graph):
                new_level_up = (ds_graphs[:ds_graph_num] + ds_up + ds_graphs[ds_graph_num+1:],)
                new_level_low = (ds_low,)
                new_levels = self._levels[:level] + new_level_up + new_level_low + self._levels[level + 1:]
                new_subvariety = IrreducibleRealLinearSubvariety(new_levels)
                assert new_subvariety.num_levels() == self.num_levels() + 1, (new_subvariety.num_levels(), self.num_levels())
                assert new_subvariety.projective_dimension() == self.projective_dimension() - 1
                ans.append(new_subvariety)
        return ans

    def multiscale_compactification(self):
        return MultiscaleCompactification(self)


# TODO: we should store more globally a list of DS graphs to avoid recomputations
# TODO: if the goal is only to compute components, then in vertical degenerations
# it is enough to degenerate only the level 0
class MultiscaleCompactification:
    r"""
    EXAMPLES:

    The example of H(2)::

        sage: from veerer import VeeringTriangulation
        sage: vt = VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,8,~7)(~1,~8,3)(2,7,~6)(~2,~3,4)", "RRRBBBBBB")
        sage: L = vt.linear_subvariety()
        sage: M = L.multiscale_compactification()
        sage: M  # optional - surface_dynamics
        MultiscaleCompactification of Irreducible real linear subvariety of projective dimension 3 in [[H_2(2)]] made of
        3 components in codimension 1
        5 components in codimension 2
        3 components in codimension 3

    Equivalently in Q(1,-1^5)::

        sage: vt = VeeringTriangulation("(0,1,2)(~2,3,4)(~4,5,6)", "BRBRBRR")
        sage: L = vt.linear_subvariety()
        sage: M = L.multiscale_compactification()
        sage: M  # optional - surface_dynamics
        MultiscaleCompactification of Irreducible real linear subvariety of projective dimension 3 in [[Q_0(1, -1^5)]] made of
        3 components in codimension 1
        5 components in codimension 2
        3 components in codimension 3

    The example of H(1,1)::

        sage: vt = VeeringTriangulation("(0,8,~7)(~0,~6,7)(1,11,~10)(~1,~11,4)(2,10,~9)(~2,~4,5)(3,9,~8)(~3,~5,6)", "RRRRBBBBBBBB")
        sage: L = vt.linear_subvariety()
        sage: M = L.multiscale_compactification()
        sage: M # optional - surface_dynamics
        MultiscaleCompactification of Irreducible real linear subvariety of projective dimension 4 in [[H_2(1^2)]] made of
        5 components in codimension 1
        11 components in codimension 2
        13 components in codimension 3
        6 components in codimension 4

    Equivalently in Q(2,-1^6)::

        sage: vt = VeeringTriangulation("(0,~6,7)(1,8,4)(2,~4,5)(3,~5,6)", "RRRRBBBBB")
        sage: L = vt.linear_subvariety()
        sage: L.multiscale_compactification()
        MultiscaleCompactification of Irreducible real linear subvariety of projective dimension 4 in [[Q_0(2, -1^6)]] made of
        5 components in codimension 1
        11 components in codimension 2
        13 components in codimension 3
        6 components in codimension 4
    """
    def __init__(self, L):
        self._L = L
        self._degeneration_helper = Degenerations()

        # at position (i, j) = i vertical and j horizontal degenerations
        self._components = collections.defaultdict(set)
        self._components[0, 0].add(L)
        d = L.projective_dimension()

        # vertical degenerations
        for codim in range(d - 1):
            for comp in self._components[codim, 0]:
                for comp_deg in comp.codimension_one_vertical_degenerations(degeneration_helper=self._degeneration_helper):
                    self._components[codim + 1, 0].add(comp_deg)

        for codim in range(d):
            sys.stdout.flush()
            h = 0
            has_horiz = True
            while has_horiz:
                sys.stdout.flush()
                has_horiz = False
                for comp in self._components[codim, h]:
                    for comp_deg in comp.codimension_one_horizontal_degenerations(degeneration_helper=self._degeneration_helper):
                        has_horiz = True
                        self._components[codim, h + 1].add(comp_deg)
                h += 1

    def projective_dimension(self):
        return self._L.projective_dimension()

    def components(self, codim):
        if codim < 0 or codim > self._L.projective_dimension():
            raise ValueError("invalid codimension")
        ans = []
        for i in range(codim + 1):
            j = codim - i
            if (i, j) in self._components:
                ans.extend(self._components[i, j])
        return ans

    def __repr__(self):
        if self.projective_dimension() == 0:
            return "MultiscaleCompactification {}".format(self._L)
        s = ["MultiscaleCompactification of {} made of".format(self._L)]
        for codim in range(1, self.projective_dimension() + 1):
            s.append("{} components in codimension {}".format(len(self.components(codim)), codim))
        return "\n".join(s)
