r"""
Real linear subvarieties in the moduli space of meromorphic Abelian differentials.
"""
# ****************************************************************************
#  This file is part of veerer
#
#       Copyright (C) 2024-2025 Vincent Delecroix
#                     2024-2025 Kai Fu
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


import array
import collections
import itertools
import numbers
import sys

from .automaton import DelaunayStrebelAutomaton
from .veering_triangulation import VeeringTriangulation
from .multiscale_veering_triangulation import MultiscaleVeeringTriangulation
from .strebel_graph import StrebelGraph
from .delaunay_strebel_graph import DelaunayStrebelGraph
from .polyhedron.linear_algebra import is_rank_one
from .permutation import perm_check, perm_orbit, perm_cycles

from sage.structure.richcmp import op_LT, op_LE, op_EQ, op_NE, op_GT, op_GE, rich_to_bool
from sage.misc.cachefunc import cached_method
from sage.rings.integer_ring import ZZ
from sage.matrix.constructor import matrix
from sage.libs.gap.libgap import libgap

# TODO: optimization: vertical/horizontal degenerations commute
# TODO: for each horiz/vert degeneration, we should record the multiscale structure and
#       the relabelling. In the dictionaries, keys would better be
#       MultiscaleVeeringTriangulation (whose prime components are roots of
#       elements in _components) and values some quadruple (vt, edges_low,
#       edges_up, relabelling) giving the different ways to obtain this
#       multiscale differential.
class PrimeDegenerations:
    r"""
    Helper class for computing successive degenerations of (prime) linear
    subvarieties and their decompositions in prime components.

    This class maintains the following attributes:

    - ``_components``: list of ``DelaunayStrebelGraph``

    - ``_to_components``: dictionary whose keys are the union of veering
      triangulations in the graphs in ``_components`` and the corresponding value
      is the index in ``_components``.

    - ``_horizontal_degenerations``: a list of dictionaries. The dictionary
      at position ``i`` encodes the horizontal degenerations of ``_components[i]``.
      Each key is a tuple of ordered indices ``(i1, ..., ik)`` which corresponds
      to the decomposition into prime components of a codimension one horizontal
      degeneration. The corresponding values are the triples ``(vt, edges_up,
      edges_low)`` where ``vt`` is a veering triangulation in ``_components[i]``
      and whose degeneration along the given ``edges_up`` and ``edges_low`` gives
      a WYYISWYG differential in the product of ``_components[i1]``,
      ``_components[i2]``, ..., ``_components[ik]`` (possibly after applying
      canonical relabelling).

    - ``vertical_degenerations``: similar to ``_horizontal_degenerations`` but for
      vertical degenerations. In that case, the keys are pairs of ordered tuples
      ``((i1, ..., ik), (j1, ..., jl)`` which corresponds to the prime decompositions
      of the two level obtained after degeneration.

    The data structure is updated after calls to the (low level) methods :meth:`add`,
    :meth:`compute_vertical_degenerations` and
    :meth:`compute_horizontal_degenerations`.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation
        sage: from veerer.linear_subvariety import PrimeDegenerations
        sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:2)(~4:2)", "BRRRBBRRRB")
        sage: D = PrimeDegenerations()
        sage: D
        Degenerations of 0 prime components (0 veering triangulations)
        sage: D.add(vt.delaunay_strebel_graph())
        0
        sage: D
        Degenerations of 1 prime components (446 veering triangulations)
        sage: D.compute_vertical_degenerations(0)
        sage: D
        Degenerations of 12 prime components (648 veering triangulations)
        sage: D.compute_horizontal_degenerations(0)
        sage: D
        Degenerations of 13 prime components (848 veering triangulations)

    We check below that some of the vertical degeneration information is correct::

        sage: degeneration_indices, root_degenerations = choice(list(D._vertical_degenerations[0].items()))
        sage: for vt, edges_up, edges_low in root_degenerations:
        ....:     vt_up, vt_low, _, _ = vt.degeneration(edges_up=edges_up, edges_low=edges_low, mutable=True)
        ....:     vt_up = [x[1] for x in vt_up.prime_decomposition(mutable=True)]
        ....:     vt_low = [x[1] for x in vt_low.prime_decomposition(mutable=True)]
        ....:     for comp in vt_up + vt_low:
        ....:         comp.set_canonical_labels()
        ....:         comp.set_immutable()
        ....:     indices_up = tuple(sorted(D._to_components[comp] for comp in vt_up))
        ....:     indices_low = tuple(sorted(D._to_components[comp] for comp in vt_low))
        ....:     assert degeneration_indices == (indices_up, indices_low)
    """
    def __init__(self):
        self._components = []     # list of Delaunay-Strebel graphs of prime veering triangulation
        self._to_components = {}  # mapping: veering triangulation -> position in self._components
        self._horizontal_degenerations = []  # list of dictionaries
        self._vertical_degenerations = []    # list of dictionaries

    def __repr__(self):
        return "Degenerations of {} prime components ({} veering triangulations)".format(len(self._components), len(self._to_components))

    def _check_component_number(self, component_number):
        if not isinstance(component_number, numbers.Integral):
            raise TypeError("component_number must be an integer")
        component_number = int(component_number)
        if component_number < 0 or component_number >= len(self._components):
            raise ValueError("component_number (={}) must a positive integer smaller than {}".format(component_number, len(self._components)))
        return component_number

    def find(self, ds_graph):
        r"""
        Find the Delaunay-Strebel graph ``ds_graph`` in the already computed
        list or add it to the list and return the associated index.
        """
        vt = ds_graph.root()
        if not vt.is_prime():
            raise ValueError("not prime")
        if vt in self._to_components:
            return self._to_components[vt]
        else:
            return self.add(ds_graph)

    def add(self, ds_graph):
        r"""
        Add the Delaunay-Strebel graph ``ds_graph`` in the list of prime components.
        """
        num = len(self._components)
        self._components.append(ds_graph)
        self._horizontal_degenerations.append(None)
        self._vertical_degenerations.append(None)
        for state in ds_graph._vertices:
            if isinstance(state, VeeringTriangulation):
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
        return a triple ``(known_prime_component_indices, unknown_prime_components, all_known_components_are_roots)``
        """
        all_roots = True

        if f.is_prime():
            f.set_canonical_labels()
            f.set_immutable()
            if f in self._to_components:
                component_number = self._to_components[f]
                all_roots = f == self._components[component_number].root()
                return (component_number,), (), all_roots
            else:
                return (), (f,), all_roots
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
                    all_roots = all_roots and ff == self._components[component_number].root()
                    prime_components_known.append(component_number)
                else:
                    prime_components_unknown.append(ff)
            prime_components_known.sort()
            prime_components_unknown.sort()
            return tuple(prime_components_known), tuple(prime_components_unknown), all_roots

    def compute_horizontal_degenerations(self, component_number):
        r"""
        Compute the horizontal degenerations of ``component_number``.
        """
        component_number = self._check_component_number(component_number)
        if self._horizontal_degenerations[component_number] is not None:
            return

        degenerations = []
        degenerations_prime_components = set()
        ds_graph = self._components[component_number]
        for state in ds_graph._vertices:
            if isinstance(state, VeeringTriangulation):
                for edges_up in state.horizontal_degeneration_up_edges_subsets():
                    edges_low = tuple([e for e in range(state._ne) if e not in edges_up])
                    f_up, f_low, _, _ = state.degeneration(edges_up=edges_up, edges_low=edges_low, mutable=True, check=False)
                    assert f_up is None
                    assert f_low.dimension() == state.dimension() - 1
                    known, unknown, all_roots = self.find_and_decompose(f_low)
                    if all_roots:
                        degenerations.append((state, edges_up, edges_low, known, unknown))
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
            self.add(DelaunayStrebelGraph(g))

        ans = self._horizontal_degenerations[component_number] = {}
        for state, edges_up, edges_low, known, unknown in degenerations:
            if all(x == self._components[self._to_components[x]].root() for x in unknown):
                degeneration = tuple(sorted(known + tuple(self._to_components[x] for x in unknown)))
                if degeneration not in ans:
                    ans[degeneration] = []
                ans[degeneration].append((state, edges_up, edges_low))

    def compute_vertical_degenerations(self, component_number):
        r"""
        Compute the vertical degenerations of ``component_number``.
        """
        component_number = self._check_component_number(component_number)
        if self._vertical_degenerations[component_number] is not None:
            return

        degenerations = []
        degenerations_prime_components = set()
        ds_graph = self._components[component_number]
        for state in ds_graph._vertices:
            if isinstance(state, VeeringTriangulation):
                for edges_low in state.vertical_degeneration_low_edges_subsets():
                    edges_up = tuple([e for e in range(state._ne) if e not in edges_low])
                    f_up, f_low, _, _ = state.degeneration(edges_up=edges_up, edges_low=edges_low, mutable=True, check=False)
                    assert f_up is not None, (state,)
                    # NOTE: the projectivization makes us loose one dimension
                    assert f_low.dimension() + f_up.dimension() == state.dimension()

                    # too expensive!!
                    # assert f_low.is_delaunay()
                    # too expensive!
                    # assert f_up.is_delaunay()

                    known_up, unknown_up, all_roots_up = self.find_and_decompose(f_up)
                    f_up_decomposed = tuple(known_up + unknown_up)
                    degenerations_prime_components.update(unknown_up)
                    known_low, unknown_low, all_roots_low = self.find_and_decompose(f_low)
                    f_low_decomposed = tuple(known_low + unknown_low)
                    degenerations_prime_components.update(unknown_low)
                    if all_roots_up and all_roots_low:
                        degenerations.append((state, edges_up, edges_low, known_up, known_low, unknown_up, unknown_low))

        # NOTE: since we have the full list of Delaunay cells, we do not need to run
        # the expensive Strebel -> Delaunay
        from .automaton import DelaunayStrebelAutomaton
        ds_graph = DelaunayStrebelAutomaton(backward=False)
        for state in degenerations_prime_components:
            ds_graph.add_seed(state, setup=False)
        ds_graph.run()
        assert set(state for state in ds_graph if isinstance(state, VeeringTriangulation)) == degenerations_prime_components

        for g in ds_graph._graph.connected_components_subgraphs():
            self.add(DelaunayStrebelGraph(g))

        ans = self._vertical_degenerations[component_number] = {}
        for state, edges_up, edges_low, known_up, known_low, unknown_up, unknown_low in degenerations:
            if all(x == self._components[self._to_components[x]].root() for x in unknown_up + unknown_low):
                degeneration_up = tuple(sorted(known_up + tuple(self._to_components[x] for x in unknown_up)))
                degeneration_low = tuple(sorted(known_low + tuple(self._to_components[x] for x in unknown_low)))
                degeneration = (degeneration_up, degeneration_low)
                if degeneration not in ans:
                    ans[degeneration] = []
                ans[degeneration].append((state, edges_up, edges_low))

    def compute_all(self):
        r"""
        Compute all degenerations up to dimension 0.
        """
        vpending = self.pending_vertical_degenerations()
        hpending = self.pending_horizontal_degenerations()
        while vpending or hpending:
            for i in vpending:
                self.compute_vertical_degenerations(i)
            for i in hpending:
                self.compute_horizontal_degenerations(i)
            vpending = self.pending_vertical_degenerations()
            hpending = self.pending_horizontal_degenerations()

    def codimension_one_vertical_degenerations(self, ds_graph):
        r"""
        Return the codimension one vertical degenerations of the Delaunay-Strebel graph ``ds_graph``.

        If the graph ``ds_graph`` is not already part of the stored prime
        components it will be added to the list.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: from veerer.linear_subvariety import PrimeDegenerations
            sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:2)(~4:2)", "BRRRBBRRRB")
            sage: D = PrimeDegenerations()
            sage: ds_graph = vt.delaunay_strebel_graph()
            sage: D.codimension_one_vertical_degenerations(ds_graph)
            [((DelaunayStrebelGraph(...),), (DelaunayStrebelGraph(...),)),
             ((DelaunayStrebelGraph(...),), (DelaunayStrebelGraph(...),)),
             ((DelaunayStrebelGraph(...),), (DelaunayStrebelGraph(...),)),
             ((DelaunayStrebelGraph(...),), (DelaunayStrebelGraph(...),)),
             ((DelaunayStrebelGraph(...), DelaunayStrebelGraph(...)), (DelaunayStrebelGraph(...),)),
             ((DelaunayStrebelGraph(...),), (DelaunayStrebelGraph(...),))]
        """
        component_number = self.find(ds_graph)
        self.compute_vertical_degenerations(component_number)
        ans = []
        for up, low in self._vertical_degenerations[component_number]:
            ans.append((tuple(self._components[i] for i in up), tuple(self._components[i] for i in low)))
        return ans

    def codimension_one_horizontal_degenerations(self, ds_graph):
        r"""
        Return the codimension one horizontal degenerations of the Delaunay-Strebel graph ``ds_graph``.

        If the graph ``ds_graph`` is not already part of the stored prime
        components it will be added to the list.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: from veerer.linear_subvariety import PrimeDegenerations
            sage: vt = VeeringTriangulation("(~0,1,2)(~1,3,4)(~2,5,6)(~3,~5,7)(~6,8,9)(~7,~8,~9)(0:2)(~4:2)", "BRRRBBRRRB")
            sage: D = PrimeDegenerations()
            sage: ds_graph = vt.delaunay_strebel_graph()
            sage: D.codimension_one_horizontal_degenerations(ds_graph)
            [(DelaunayStrebelGraph(...),)]

        """
        component_number = self.find(ds_graph)
        self.compute_horizontal_degenerations(component_number)
        ans = []
        for degeneration in self._horizontal_degenerations[component_number]:
            ans.append(tuple(self._components[i] for i in degeneration))
        return ans


def _convert(cls, x):
    return x if isinstance(x, cls) else cls(x)


class NodesCanonicalizer:
    r"""
    Utility class to compute canonical representatives of multiscale structure
    in a given linear subvariety.

    EXAMPLES::

        sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily, MultiscaleVeeringTriangulation
        sage: from veerer.linear_subvariety import NodesCanonicalizer

    An example with two possible prong matchings::

        sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
        sage: vt1 = VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)])
        sage: C = NodesCanonicalizer([[vt0.delaunay_strebel_graph()], [vt1.delaunay_strebel_graph()]])
        sage: list(C.horizontal_nodes(0, 0))
        []
        sage: list(C.horizontal_nodes(1, 0))
        []
        sage: C.prong_matchings()[0]
        ((0, 0, 0, 1, 0, 0, 0), (0, 0, 0, 1, 0, 1, 0))
        sage: C._levels[0][0].root().stratum()  # optional - surface_dynamics
        H_1(0)
        sage: C._levels[1][0].root().stratum()  # optional - surface_dynamics
        H_1(2, -2)

        sage: C.libgap_group().Size()
        2

        sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]], horizontal_nodes=[[[]], [[]]], prong_matchings=[((0, 0, 0, 0), (1, 0, 1, 0))])
        sage: C.canonical_multiscale_structure(mvt)
        MultiscaleVeeringTriangulation(
          veering_triangulations=[
            [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])],
            [VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)])]
          ],
          horizontal_nodes=[[[]], [[]]],
          prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0))]
        )

    An example with three levels::

        sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
        sage: vt1 = VeeringTriangulationLinearFamily("(0:2,~0:2)", "R", [(1)])
        sage: vt2 = VeeringTriangulationLinearFamily("(0:3)(~0:3)", "R", [(1)])
        sage: C = NodesCanonicalizer([[vt0.delaunay_strebel_graph()], [vt1.delaunay_strebel_graph()], [vt2.delaunay_strebel_graph()]])
        sage: C._levels[0][0].root().stratum()  # optional - surface_dynamics
        H_1(0)
        sage: C._levels[1][0].root().stratum()  # optional - surface_dynamics
        H_0(0^2, -2)
        sage: C._levels[2][0].root().stratum()  # optional - surface_dynamics
        H_0(2, -2^2)
        sage: mvt = MultiscaleVeeringTriangulation([[vt0], [vt1], [vt2]], horizontal_nodes=[[[]], [[]], [[]]], prong_matchings=[((0, 0, 0, 0), (1, 0, 1, 0)), ((1, 0, 0, 0), (2, 0, 0, 1)), ((1, 0, 1, 0), (2, 0, 1, 1))])
        sage: C.canonical_multiscale_structure(mvt)
        MultiscaleVeeringTriangulation(
          veering_triangulations=[
            [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])],
            [VeeringTriangulationLinearFamily("(0:2,~0:2)", "R", [(1)])],
            [VeeringTriangulationLinearFamily("(0:3)(~0:3)", "R", [(1)])]
          ],
          horizontal_nodes=[[[]], [[]], [[]]],
          prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((1, 0, 0, 0), (2, 0, 0, 0)), ((1, 0, 1, 0), (2, 0, 1, 0))]
        )

    An example with a single level::

        sage: vt = VeeringTriangulationLinearFamily("(0:1)(~0:1,1:1)(~1:1,2:1)(~2:1)", "RRR", [(1, 0, 1), (0, 1, 0)])
        sage: C = NodesCanonicalizer([[vt.delaunay_strebel_graph()]])
        sage: C.libgap_group().Size()
        2

    An example with two prime components in level -1::

        sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,~5)", "RRBBRR", [(1, 0, -1, -1, 0, -1), (0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1)])
        sage: vt1 = VeeringTriangulation("(0:2,~0:2)", "R")
        sage: C = NodesCanonicalizer([[vt0.delaunay_strebel_graph()], [vt1.delaunay_strebel_graph()] * 2])
        sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1] * 2], prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 1, 0), (1, 1, 0, 0))])
        sage: C.libgap_group().Size()
        16
        sage: C.canonical_multiscale_structure(mvt)
        MultiscaleVeeringTriangulation(
          veering_triangulations=[
            [VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,~5)", "RRBBRR", [(1, 0, -1, -1, 0, -1), (0, 1, 1, 1, 0, 1), (0, 0, 0, 0, 1, 1)])],
            [VeeringTriangulation("(0:2,~0:2)", "R"), VeeringTriangulation("(0:2,~0:2)", "R")]
          ],
          horizontal_nodes=[[[]], [[], []]],
          prong_matchings=[((0, 0, 0, 0), (1, 0, 0, 0)), ((0, 0, 1, 0), (1, 1, 0, 0))]
        )

    """
    HN = 0    # code for horizontal node
    PM = 1    # code for prong matching

    def __init__(self, ds_graphs):
        self._levels = ds_graphs

        from sage.features.gap import GapPackage
        GapPackage("images").require()

    def _normalize_prong_matching(self, l0, c0, h0, a0, l1, c1, h1, a1):
        r"""
        Return a normalized triple (hh0, hh1, aa1)
        """
        vt0 = self._levels[l0][c0].root()
        vt1 = self._levels[l1][c1].root()
        h1, a1 = vt1._normalize_face_separatrix(h1, a1)
        for (hh0, aa0), (hh1, aa1) in zip(vt0.vertex_separatrices(h0, a0), vt1.face_separatrices(h1, a1)):
            if (hh0, aa0) < (h0, a0):
                h0 = hh0
                a0 = aa0
                h1 = hh1
                a1 = aa1
        assert a0 == 0
        return (h0, h1, a1)

    def infinite_cylinder_representatives(self, level, component):
        r"""
        Return a sorted list of (potential) horizontal nodes as quadruples (l, c, h0, h1).
        """
        ds_graph = self._levels[level][component]
        vt = ds_graph.root()
        cyls = []
        for face in perm_cycles(vt._fp):
            if all(vt._bdry[i] == 1 and vt._colouring[i // 2] == vt._colouring[face[0] // 2] for i in face):
                # pole of angle zero
                cyls.append(min(face))
        return tuple(cyls)

    # TODO: this should be moved to VeeringTriangualtion
    def double_pole_residues(self, level, component):
        vt = self._levels[level][component].root()
        ne = vt._ne
        colouring = vt._colouring
        fp = vt._fp

        cyls = self.infinite_cylinder_representatives(level, component)
        r = matrix(ZZ, len(cyls), ne)
        for i, h in enumerate(cyls):
            o = 1
            for h0 in perm_orbit(fp, h):
                r[i, h0 // 2] += o

                h1 = fp[h0]
                if vt.half_edge_num_separatrices(h1) % 2 == 0:
                    o *= -1
        return r

    def horizontal_nodes(self, level, component):
        r"""
        EXAMPLES::

            sage: from veerer.linear_subvariety import NodesCanonicalizer
            sage: from veerer import VeeringTriangulationLinearFamily, MultiscaleVeeringTriangulation
            sage: vt = VeeringTriangulationLinearFamily("(0:1)(~0:1,1:1)(~1:1,2:1)(~2:1)", "RRR", [(1, 0, 1), (0, 1, 0)])
            sage: C = NodesCanonicalizer([[vt.delaunay_strebel_graph()]])
            sage: list(C.horizontal_nodes(0, 0))
            [(0, 5), (1, 3)]
        """
        vt = self._levels[level][component].root()
        residues = self.double_pole_residues(level, component) * vt.generators_matrix().transpose()
        by_residues = collections.defaultdict(list)
        for h, r in zip(self.infinite_cylinder_representatives(level, component), residues):
            if r[r.nonzero_positions()[0]] < 0:
                r *= -1
            r.set_immutable()
            by_residues[r].append(h)

        return itertools.chain(*[itertools.combinations(cyl_reps, 2) for cyl_reps in by_residues.values()])

    def separatrix_representatives(self):
        r"""
        Return the pair ``(vertex_separatrices, face_separatrices)`` of
        respectively vertex separatrices and face separatrices that could occur
        in a (normalized) prong matching.
        """
        vertex_separatrices = [[[] for _ in range(len(self._levels[level]))] for level in range(len(self._levels))]
        face_separatrices = [[[] for _ in range(len(self._levels[level]))] for level in range(len(self._levels))]

        zeros = collections.defaultdict(list)  # list of waiting separatrices

        for l1, ds_graphs in enumerate(self._levels):
            new_zeros = collections.defaultdict(list)
            for c1, ds_graph in enumerate(ds_graphs):
                vt = ds_graph.root()

                for vseps in vt.vertex_separatrices(flat=False):
                    assert vseps[0][1] == 0
                    new_zeros[len(vseps)].append((l1, c1, vseps[0][0]))

                for fseps in vt.face_separatrices(flat=False):
                    assert fseps[0][1] == 0
                    order = len(fseps)

                    if zeros[order]:
                        for l, c, vsep in zeros[order]:
                            vertex_separatrices[l][c].append(vsep)
                        zeros[order].clear()
                        face_separatrices[l1][c1].extend(fseps)

            for x, y in new_zeros.items():
                zeros[x].extend(y)
            new_zeros.clear()

        return tuple(vertex_separatrices), tuple(face_separatrices)

    def prong_matchings(self):
        r"""
        Return a sorted list of (potential) prong matchings as 7-tuples (l0, c0, h0, l1, c1, h1, a1).

        EXAMPLES::

            sage: from veerer import VeeringTriangulation, VeeringTriangulationLinearFamilies
            sage: from veerer.linear_subvariety import NodesCanonicalizer

            sage: vt0 = VeeringTriangulation("(0:1)(~0:1)", "R")
            sage: vt1 = VeeringTriangulation("(0:3)(~0:3)", "R")
            sage: ds_graph0 = VeeringTriangulationLinearFamilies.diagonal(vt0, [1, 1, 1, 1]).delaunay_strebel_graph()
            sage: ds_graph1 = VeeringTriangulationLinearFamilies.diagonal(vt1, [1, 1]).delaunay_strebel_graph()
            sage: pms, pm_from, pm_to = NodesCanonicalizer([[ds_graph0], [ds_graph1]]).prong_matchings()
            sage: pms
            ((0, 0, 0, 1, 0, 0, 0),
             (0, 0, 0, 1, 0, 0, 1),
             (0, 0, 2, 1, 0, 0, 0),
             (0, 0, 2, 1, 0, 0, 1),
             ...
             (0, 0, 6, 1, 0, 3, 1))
        """
        prong_matchings_from = [[[] for _ in range(len(self._levels[level]))] for level in range(len(self._levels))]
        prong_matchings_to = [[[] for _ in range(len(self._levels[level]))] for level in range(len(self._levels))]
        pms = []

        zeros = collections.defaultdict(list)

        for l1, ds_graphs in enumerate(self._levels):
            new_zeros = collections.defaultdict(list)
            for c1, ds_graph in enumerate(ds_graphs):
                vt = ds_graph.root()

                for vseps in vt.vertex_separatrices(flat=False):
                    assert vseps[0][1] == 0
                    new_zeros[len(vseps)].append((l1, c1, vseps[0][0]))

                for fseps in vt.face_separatrices(flat=False):
                    assert fseps[0][1] == 0
                    order = len(fseps)

                    for (l0, c0, h0) in zeros[order]:
                        for h1, a1 in fseps:
                            pm = (l0, c0, h0, l1, c1, h1, a1)
                            pms.append(pm)
                            prong_matchings_from[l0][c0].append(pm)
                            prong_matchings_to[l1][c1].append(pm)

            for x, y in new_zeros.items():
                zeros[x].extend(y)
            new_zeros.clear()

        return tuple(pms), prong_matchings_from, prong_matchings_to

    def vertices(self):
        for level, ds_graphs in enumerate(self._levels):
            for component, ds_graph in enumerate(ds_graphs):
                yield (level, component, ds_graph)

    @cached_method
    def ambient_domain(self):
        r"""
        Return the dictionary mapping the infinite cylinder and separatrix
        representatives to integers and is used in communication with libgap.
        """
        dom = []
        to_dom = {}

        # horizontal nodes
        for level, component, _ in self.vertices():
            for h0, h1 in self.horizontal_nodes(level, component):
                elt = (self.HN, level, component, h0, h1)
                dom.append(elt)
                to_dom[elt] = len(to_dom)

        # prong matchings
        for pm in self.prong_matchings()[0]:
            elt = (self.PM,) + pm
            dom.append(elt)
            to_dom[elt] = len(to_dom)

        return dom, to_dom

    def monodromy_permutation(self, level, component, g):
        r"""
        Convert the monodromy element ``g`` of ``(level, component)`` into a permutation of the domain.
        """
        domain, to_domain = self.ambient_domain()

        ds_graph = self._levels[level][component]
        vt = ds_graph.root()
        g_vseps, g_fseps, g_cyls, g_fhedges = vt.framing_group_element_permutation(g, ds_graph.framing(0))

        p = array.array('i', range(len(to_domain)))

        # action on horizontal nodes
        for h0, h1 in self.horizontal_nodes(level, component):
            hh0 = min(perm_orbit(vt._fp, g_cyls[h0]))
            hh1 = min(perm_orbit(vt._fp, g_cyls[h1]))
            if hh1 < hh0:
                hh0, hh1 = hh1, hh0
            i = to_domain[self.HN, level, component, h0, h1]
            j = to_domain[self.HN, level, component, hh0, hh1]
            p[i] = j

        # action on prong matchings
        prong_matchings, prong_matchings_from, prong_matchings_to = self.prong_matchings()
        for (l0, c0, h0, l1, c1, h1, a1) in prong_matchings_from[level][component]:
            assert l0 == level and c0 == component, (level, component, l0, c0)
            hh0, aa0 = g_vseps[h0, 0]
            hh0, hh1, aa1 = self._normalize_prong_matching(l0, c0, hh0, aa0, l1, c1, h1, a1)
            i = to_domain[self.PM, l0, c0, h0, l1, c1, h1, a1]
            j = to_domain[self.PM, l0, c0, hh0, l1, c1, hh1, aa1]
            p[i] = j

        for (l0, c0, h0, l1, c1, h1, a1) in prong_matchings_to[level][component]:
            assert l1 == level and c1 == component, (level, component, l1, c1)
            hh1, aa1 = g_fseps[h1, a1]
            # NOTE: since we do not act on level l0, the prong matching is already normalized
            i = to_domain[self.PM, l0, c0, h0, l1, c1, h1, a1]
            j = to_domain[self.PM, l0, c0, h0, l1, c1, hh1, aa1]
            p[i] = j

        # TODO: remove check
        perm_check(p)
        return p

    def isomorphic_prime_component_partition(self, level):
        by_prime_comp = collections.defaultdict(list)
        for comp, ds_graph in enumerate(self._levels[level]):
            by_prime_comp[ds_graph].append(comp)
        return tuple(map(tuple, by_prime_comp.values()))

    def isomorphism_generators(self, level):
        domain, to_domain = self.ambient_domain()
        gens = []
        prong_matchings, prong_matchings_from, prong_matchings_to = self.prong_matchings()
        for components in self.isomorphic_prime_component_partition(level):
            ds_graph = self._levels[level][components[0]]
            root = ds_graph.root()

            # symmetries of isomorphic prime components
            horizontal_nodes = self.horizontal_nodes(level, components[0])
            if len(components) == 2:
                p = array.array('i', range(len(to_domain)))
                for h0, h1 in self.horizontal_nodes(level, components[0]):
                    i = to_domain[self.HN, level, components[0], h0, h1]
                    j = to_domain[self.HN, level, components[1], h0, h1]
                    p[i] = j
                    p[j] = i
                for (l0, c0, h0, l1, c1, h1, a1) in prong_matchings_from[level][components[0]]:
                    i = to_domain[self.PM, l0, components[0], h0, l1, c1, h1, a1]
                    j = to_domain[self.PM, l0, components[1], h0, l1, c1, h1, a1]
                    p[i] = j
                    p[j] = i
                for (l0, c0, h0, l1, c1, h1, a1) in prong_matchings_to[level][components[0]]:
                    i = to_domain[self.PM, l0, c0, h0, l1, components[0], h1, a1]
                    j = to_domain[self.PM, l0, c0, h0, l1, components[1], h1, a1]
                    p[i] = j
                    p[j] = i
                perm_check(p)
                gens.append(p)

            if len(components) >= 3:
                p = array.array('i', range(len(to_domain)))
                for k in range(len(components)):
                    comp0 = components[k]
                    comp1 = components[(k + 1) % len(components)]
                    for h in cyls:
                        i = to_domain[self.HN, level, comp0, h0, h1]
                        j = to_domain[self.HN, level, comp1, h0, h1]
                        p[i] = j
                    for (l0, c0, h0, l1, c1, h1, a1) in prong_matchings_from[level, components[0]]:
                        i = to_domain[self.PM, l0, comp0, h0, l1, c1, h1, a1]
                        j = to_domain[self.PM, l0, comp1, h0, l1, c1, h1, a1]
                        p[i] = j
                    for (l0, c0, h0, l1, c1, h1, a1) in prong_matchings_to[level, components[0]]:
                        i = to_domain[self.PM, l0, c0, h0, l1, comp0, h1, a1]
                        j = to_domain[self.PM, l0, c0, h0, l1, comp1, h1, a1]
                        p[i] = j
                perm_check(p)
                gens.append(p)

                # symmetries of given prime component
                for aut in root.automorphism_gens():
                    g = ds_graph.automorphism_framing_monodromy(aut)
                    p = self.monodromy_permutation(level, components[0], g)
                    gens.append(p)

        return tuple(gens)

    @cached_method
    def libgap_group(self):
        gens = []
        for level, ds_graphs in enumerate(self._levels):
            for p in self.isomorphism_generators(level):
                gens.append(libgap.PermList([i + 1 for i in p]))

            # NOTE: it is enough to only use monodromy generator once per isomorphism class of DS graphs
            # since symmetry generators are present
            for components in self.isomorphic_prime_component_partition(level):
                component = components[0]
                ds_graph = self._levels[level][component]
                for g in ds_graph.framing_group().gens():
                    p = self.monodromy_permutation(level, component, g)
                    gens.append(libgap.PermList([i + 1 for i in p]))

        return libgap.Group(gens)

    # TODO: add examples
    def multiscale_structure_libgap_encoding(self, mvt):
        if not isinstance(mvt, MultiscaleVeeringTriangulation):
            raise TypeError
        if len(mvt._veering_triangulations) != len(self._levels):
            raise ValueError("invalid multiscale veering triangulation")
        for level, (veering_triangulations, ds_graphs) in enumerate(zip(mvt._veering_triangulations, self._levels)):
            if len(veering_triangulations) != len(ds_graphs):
                raise ValueError("invalid multiscale veering triangulation")
            for component, (vt, ds_graph) in enumerate(zip(veering_triangulations, ds_graphs)):
                if vt != ds_graph.root():
                    raise ValueError("invalid multiscale veering triangulation")

        # turn horizontal and vertical nodes of mvt into the domain
        domain, to_domain = self.ambient_domain()
        nodes_encoding = []
        horizontal_nodes = mvt._horizontal_nodes()
        prong_matchings = mvt._prong_matchings()
        for level, component, ds_graph in self.vertices():
            for (h0, h1) in horizontal_nodes[level][component]:
                nodes_encoding.append(1 + to_domain[self.HN, level, component, h0, h1])
        for (l0, c0, h0, a0), (l1, c1, h1, a1) in mvt._prong_matchings():
            nodes_encoding.append(1 + to_domain[self.PM, l0, c0, h0, l1, c1, h1, a1])
        nodes_encoding.sort()
        return libgap(nodes_encoding)

    # TODO: add examples
    def multiscale_structure_libgap_decoding(self, nodes):
        domain, to_domain = self.ambient_domain()
        horizontal_nodes = [[[] for _ in range(len(self._levels[level]))] for level in range(len(self._levels))]
        prong_matchings = []
        for i in nodes:
            elt = domain[i - 1]
            if elt[0] == self.HN:
                _, l, c, h0, h1 = elt
                horizontal_nodes[l][c].append((h0, h1))
            elif elt[0] == self.PM:
                _, l0, c0, h0, l1, c1, h1, a1 = elt
                prong_matchings.append(((l0, c0, h0, 0), (l1, c1, h1, a1)))
            else:
                raise ValueError

        return MultiscaleVeeringTriangulation([[ds_graph.root() for ds_graph in ds_graphs] for ds_graphs in self._levels],
                                              horizontal_nodes=horizontal_nodes,
                                              prong_matchings=prong_matchings)

    def canonical_multiscale_structure(self, mvt):
        r"""
        Return a canonical multiscale veering triangulation in the same linear subvariety
        as ``mvt``.

        INPUT:

        - ``mvt`` - a :class:`MultiscaleVeeringTriangulation` whose veering
          triangulations and level structure coincide with the levels provided as
          input to this canonicalizer.
        """
        P = self.libgap_group()
        enc = self.multiscale_structure_libgap_encoding(mvt)
        enc_canonical = libgap.CanonicalImage(P, enc, libgap.OnSets)
        return self.multiscale_structure_libgap_decoding(enc_canonical)



# TODO: add examples
class IrreducibleRealLinearSubvariety:
    r"""
    Irreducible real linear subvariety of the moduli space of multiscale
    Abelian or quadratic differentials.

    Note that each level is decomposed into prime components.

    TESTS::

        sage: from veerer import VeeringTriangulationLinearFamily, MultiscaleVeeringTriangulation
        sage: from veerer.linear_subvariety import IrreducibleRealLinearSubvariety
        sage: vt0 = VeeringTriangulationLinearFamily("(0,1,2)(~0,~1,~2)", "RRB", [(1, 0, -1), (0, 1, 1)])
        sage: vt1 = VeeringTriangulationLinearFamily("(0:1,1:1,~0:1,~1:1)", "RB", [(1, 0), (0, 1)])
        sage: mvt = MultiscaleVeeringTriangulation(veering_triangulations=[[vt0], [vt1]], horizontal_nodes=[[[]], [[]]], prong_matchings=[((0, 0, 0, 0), (1, 0, 1, 0))])
        sage: L = IrreducibleRealLinearSubvariety([[vt0.delaunay_strebel_graph()], [vt1.delaunay_strebel_graph()]], mvt)
    """
    # TODO: simplify the constructor. It should __init__(self, ds_graphs, mvt=None)
    # for StrebelGraph, VeeringTriangulations and linear families, building the associated linear subvariety
    # should be done with the method .linear_subvariety()
    def __init__(self, *args, canonicalizer=None):
        # list of dictionaries: self._levels[i] is a tuple representing the
        # i-th level
        if len(args) == 1:
            if isinstance(args[0], VeeringTriangulation):
                if not args[0].is_prime():
                    raise ValueError("invalid input: veering triangulation must be prime")
                multiscale_veering_triangulation = MultiscaleVeeringTriangulation([args[0]], mutable=True)
            elif not isinstance(args[0], MultiscaleVeeringTriangulation):
                raise ValueError("input must be a multiscale veering triangulation; got {}".format(type(args[0]).__name__))
            else:
                multiscale_veering_triangulation = args[0].copy(mutable=True)
            ds_graphs = [[vt.delaunay_strebel_graph() for vt in vts] for vts in multiscale_veering_triangulation._veering_triangulations]
        elif len(args) == 2:
            ds_graphs, multiscale_veering_triangulation = args
            if multiscale_veering_triangulation is not None:
                multiscale_veering_triangulation = multiscale_veering_triangulation.copy(mutable=True)

        if isinstance(ds_graphs, (tuple, list)):
            ds_graphs_new = []
            for elt in ds_graphs:
                if isinstance(elt, (tuple, list)):
                    level = []
                    for x in elt:
                        x = _convert(DelaunayStrebelGraph, x)
                        level.append(x)
                else:
                    level = [_convert(DelaunayStrebelGraph, elt)]
                ds_graphs_new.append(level)
            ds_graphs = ds_graphs_new
        else:
            ds_graphs = [[_convert(DelaunayStrebelGraph, ds_graphs)]]

        # Check that the mvt coincide with the roots of our ds_graphs
        if multiscale_veering_triangulation is not None:
            if len(multiscale_veering_triangulation._veering_triangulations) != len(ds_graphs):
                raise ValueError("different number of levels")
            for i, (vts, level_ds_graphs) in enumerate(zip(multiscale_veering_triangulation._veering_triangulations, ds_graphs)):
                if len(vts) != len(level_ds_graphs):
                    raise ValueError("different number of components at level {}".format(i))
                for vt, ds_graph in zip(vts, level_ds_graphs):
                    if vt != ds_graph.root():
                        raise ValueError("invalid multiscale veering triangulation")

        # Permute each level so that they are sorted
        for level, level_ds_graphs in enumerate(ds_graphs):
            new_ds_graphs = sorted((comp, i) for i, comp in enumerate(level_ds_graphs))
            perm = [-1] * len(level_ds_graphs)
            for j, (comp, i) in enumerate(new_ds_graphs):
                perm[i] = j
            ds_graphs[level] = [comp for comp, i in new_ds_graphs]
            if multiscale_veering_triangulation is not None:
                multiscale_veering_triangulation.permute_level(level, perm)

        self._levels = tuple(map(tuple, ds_graphs))
        self._mvt = multiscale_veering_triangulation

        self._check()

        if multiscale_veering_triangulation is not None:
            if canonicalizer is None:
                canonicalizer = NodesCanonicalizer(self._levels)
            self._mvt = canonicalizer.canonical_multiscale_structure(multiscale_veering_triangulation)
            self._mvt.set_immutable()
            self._check()

    def _check_level(self, level):
        if not isinstance(level, numbers.Integral):
            raise ValueError("level must be an integer")
        level = int(level)
        if level < 0:
            level = -level
        if not (0 <= level < len(self._levels)):
            raise IndexError("level out of range")
        return level

    def _check(self, error=RuntimeError):
        if not (isinstance(self._levels, tuple) and
                all(isinstance(level, tuple) and
                    level and
                    all(isinstance(elt, DelaunayStrebelGraph) for elt in level)
                    for level in self._levels)):
            raise error

        if self._mvt is not None:
            if not isinstance(self._mvt, MultiscaleVeeringTriangulation):
                raise error

            if self._mvt.num_levels() != len(self._levels):
                raise error

            for stgraphs, vts in zip(self._levels, self._mvt._veering_triangulations):
                if len(stgraphs) != len(vts):
                    raise error
                for stgraph, vt in zip(stgraphs, vts):
                    if vt != stgraph.root():
                        raise error

    def __eq__(self, other):
        if type(self) is not type(other):
            return False

        return self._levels == other._levels and self._mvt == other._mvt

    def __ne__(self, other):
        return not (self == other)

    def __lt__(self, other):
        if type(self) is not type(other):
            raise TypeError

        return len(self._levels) < len(other._levels) or self._levels < other._levels or self._mvt < other._mvt

    def __hash__(self):
        return (2137573 * hash(self._levels)) ^ (13325 * hash(self._mvt))

    def __len__(self):
        r"""
        Return the number of levels.
        """
        return len(self._levels)

    num_levels = __len__

    def __repr__(self):
        return "Irreducible real linear subvariety of projective dimension {} in {}".format(self.projective_dimension(), self.ambient_stratum(multiscale_structure=True))

    def levels(self):
        r"""
        Return the set of levels
        """
        return range(len(self._levels))

    def signature(self, level=None):
        r"""
        Return the signature (ie order of zeros).

        If level is provided, return a list of degrees. Otherwise, return a
        list of lists.
        """
        if level is None:
            return tuple(self.signature(level) for level in self.levels())
        level = self._check_level(level)
        return tuple(sorted(sum((comp.root().stratum().signature() for comp in self._levels[level]), tuple())))

    def ambient_stratum(self, multiscale_structure=False):
        r"""
        Return the ambient stratum of this subvariety.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,8,~7)(~0,~6,7)(1,9,~8)(~1,~11,4)(2,10,~9)(~2,~4,5)(3,11,~10)(~3,~5,6)", "RRRRBBBBBBBB")
            sage: L = vt.linear_subvariety()
            sage: L.ambient_stratum()  # optional - surface_dynamics
            H_1(0^4)
            sage: for Ldeg in sorted(L.codimension_one_vertical_degenerations()):  # optional - surface_dynamics
            ....:     print(Ldeg.ambient_stratum(), Ldeg.ambient_stratum(multiscale_structure=True))
            H_1(0^4) [[H_1(0)], [H_0(0^4, -2)]]
            H_1(0^4) [[H_1(0)], [H_0(0^4, -2)]]
            H_1(0^4) [[H_1(0^2)], [H_0(0^3, -2)]]
            H_1(0^4) [[H_1(0^2)], [H_0(0^3, -2)]]
            H_1(0^4) [[H_1(0^2)], [H_0(0^2, -2), H_0(0^2, -2)]]
            H_1(0^4) [[H_1(0^2)], [H_0(0^2, -2), H_0(0^2, -2)]]
            H_1(0^4) [[H_1(0^3)], [H_0(0^2, -2)]]
            H_1(0^4) [[H_1(0^3)], [H_0(0^2, -2)]]
        """
        return self._mvt.ambient_stratum(multiscale_structure=multiscale_structure)

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
            4
            4
            4
            4
            4
        """
        if level is None:
            return sum(self.dimension(level) for level in self.levels())
        level = self._check_level(level)
        return sum(comp.root().dimension() for comp in self._levels[level])

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
            2
            2
            2
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

    # TODO: now that degeneration implements multiscale structure the output is much bigger
    # double check it is correct
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
            [Irreducible real linear subvariety of projective dimension 2 in [[H_1(2, -1^2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(2, -1^2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(2, -1^2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(2, -1^2)]]]

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

        mvt = self._mvt

        level = self._check_level(level)

        if degeneration_helper is None:
            degeneration_helper = PrimeDegenerations()

        ds_graphs = self._levels[level]
        ans = []
        for component, ds_graph in enumerate(ds_graphs):
            ds_graph_index = degeneration_helper.find(ds_graph)
            degeneration_helper.compute_horizontal_degenerations(ds_graph_index)

            for indices, degenerations in degeneration_helper._horizontal_degenerations[ds_graph_index].items():
                # linear subvariety without node information
                ds_degeneration = tuple(degeneration_helper._components[i] for i in indices)
                new_level = ds_graphs[:component] + ds_degeneration + ds_graphs[component + 1:]
                new_levels = self._levels[:level] + (new_level,) + self._levels[level + 1:]

                if mvt is None:
                    new_subvariety = IrreducibleRealLinearSubvariety(new_levels, None)
                    ans.append(new_subvariety)
                    continue

                root_framing = ds_graph.framing(0)
                for (vt, edges_up, edges_low) in degenerations:
                    # (possible) TODO (for later): we could avoid the call to
                    # to degeneration here by moving all the relevant
                    # information into PrimeDegenerations
                    # TODO: making a full copy is a bit too much. We just need to
                    # replace a single prime component
                    vt_framing = ds_graph.framing(ds_graph.vertex_index(vt))
                    oldmvt = mvt.copy(mutable=True)
                    oldmvt.replace_veering_triangulation(level, component, vt, vt_framing, root_framing)
                    newmvt = oldmvt.degeneration(level, component, edges_low=edges_low, edges_up=edges_up)
                    new_vt = newmvt._veering_triangulations[level][component]
                    newmvt = newmvt.prime_decomposition(level, component)
                    newmvt = newmvt.copy(mutable=True)
                    for i in range(len(new_vt.prime_decomposition())):
                        newmvt.set_canonical_labels(level, component + i)
                    newmvt.set_immutable()
                    new_subvariety = IrreducibleRealLinearSubvariety(new_levels, newmvt)
                    assert new_subvariety.projective_dimension() == self.projective_dimension() - 1
                    assert new_subvariety.num_levels() == self.num_levels()
                    ans.append(new_subvariety)

                    # TODO: this step is not completed yet. We will apply
                    # monodromy group to the elements in the `representatives`
                    # later.

        return ans

    # TODO: now that we have multiscale structure implemented in degenerations we obtain
    # linear subvarieties with identical prime components but different multiscale structures.
    # double check that the answers are correct.
    def codimension_one_vertical_degenerations(self, level=None, degeneration_helper=None):
        r"""
        Return the list of codiemsnion one vertical degenerations as a list of Delauany-Strebel automata.

        EXAMPLES::

            sage: from veerer import *

            sage: vt = VeeringTriangulation("(0,1,2)(~1,3,4)(~3,5,6)(~6,~2,~5)(~4,7,8)(~8,~0,~7)", "RBBBRRBBR")
            sage: L = vt.linear_subvariety()
            sage: L # optional - surface_dynamics
            Irreducible real linear subvariety of projective dimension 3 in [[H_2(2)]]
            sage: deg_first = sorted(L.codimension_one_vertical_degenerations()) # optional - surface_dynamics
            sage: deg_first # optional - surface_dynamics
            [Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0^2)], [H_0(2, -2^2)]]]
            sage: deg_second = []
            sage: for L1 in deg_first: # optional - surface_dynamics
            ....:     degs = sorted(L1.codimension_one_vertical_degenerations())
            ....:     print(L1, degs)
            ....:     deg_second.extend(degs)
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]], Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]], Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]], Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]], Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]], Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]], Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            Irreducible real linear subvariety of projective dimension 2 in [[H_1(0^2)], [H_0(2, -2^2)]] [Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]], Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            sage: for L2 in deg_second: # optional - surface_dynamics
            ....:     assert not list(L2.codimension_one_vertical_degenerations())
        """
        if level is None:
            return [degeneration for level in self.levels() for degeneration in self.codimension_one_vertical_degenerations(level, degeneration_helper)]

        mvt = self._mvt

        level = self._check_level(level)

        if degeneration_helper is None:
            degeneration_helper = PrimeDegenerations()

        ds_graphs = self._levels[level]
        ans = []
        for component, ds_graph in enumerate(ds_graphs):
            i = degeneration_helper.find(ds_graph)
            degeneration_helper.compute_vertical_degenerations(i)

            for (indices_up, indices_low), degenerations in degeneration_helper._vertical_degenerations[i].items():
                # linear subvariety without node information
                ds_up = tuple(degeneration_helper._components[i] for i in indices_up)
                ds_low = tuple(degeneration_helper._components[i] for i in indices_low)
                new_level_up = (ds_graphs[:component] + ds_up + ds_graphs[component + 1:],)
                new_level_low = (ds_low,)
                new_levels = self._levels[:level] + new_level_up + new_level_low + self._levels[level + 1:]

                if mvt is None:
                    new_subvariety = IrreducibleRealLinearSubvariety(new_levels, None)
                    ans.append(new_subvariety)
                    continue

                root_framing = ds_graph.framing(0)
                for (vt, edges_up, edges_low) in degenerations:
                    vt_framing = ds_graph.framing(ds_graph.vertex_index(vt))
                    oldmvt = mvt.copy(mutable=True)
                    oldmvt.replace_veering_triangulation(level, component, vt, vt_framing, root_framing)
                    newmvt = oldmvt.degeneration(level, component, edges_low=edges_low, edges_up=edges_up)
                    new_vt1 = newmvt._veering_triangulations[level][component]
                    new_vt2 = newmvt._veering_triangulations[level + 1][0]
                    newmvt = newmvt.prime_decomposition(level, component)
                    newmvt = newmvt.prime_decomposition(level + 1, 0)                    
                    newmvt = newmvt.copy(mutable=True)
                    for i in range(len(new_vt1.prime_decomposition())):
                        newmvt.set_canonical_labels(level, component + i)
                    for i in range(len(new_vt2.prime_decomposition())):
                        newmvt.set_canonical_labels(level + 1, i)
                    newmvt.set_immutable()
                    new_subvariety = IrreducibleRealLinearSubvariety(new_levels, newmvt)
                    assert new_subvariety.num_levels() == self.num_levels() + 1, (new_subvariety.num_levels(), self.num_levels())
                    assert new_subvariety.projective_dimension() == self.projective_dimension() - 1
                    ans.append(new_subvariety)

                    # TODO: this step is not completed yet. We will apply
                    # monodromy group to the elements in the `representatives`
                    # later.

        return ans

    def multiscale_compactification(self):
        r"""
        Return the multiscale compactification of this linear subvariety.
        """
        return MultiscaleCompactification(self)



# TODO: make degeneration works for folded edges
# TODO: this class could also easily handle LinearSubvariety by not performing
# any degeneration but accepting a linear family as input
# TODO: since we have multiscale structure implemented in degenerations, the output for H(1,1)
# changed from (5, 11, 13, 6) to (5, 11, 14, 6). Double check it is correct.
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
        sage: d = M.projective_dimension()
        sage: for codim in range(d):
        ....:   for component in M.components(codim):
        ....:      assert component.ambient_stratum() == L.ambient_stratum()

    Equivalently in Q(1,-1^5)::

        sage: vt = VeeringTriangulation("(0,1,2)(~2,3,4)(~4,5,6)", "BRBRBRR")
        sage: L = vt.linear_subvariety()
        sage: M = L.multiscale_compactification()  # not tested (folded edge)
        sage: M  # optional - surface_dynamics  # not tested (folded edge)
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
        14 components in codimension 3
        6 components in codimension 4
        sage: d = M.projective_dimension()
        sage: for codim in range(d):
        ....:   for component in M.components(codim):
        ....:      assert component.ambient_stratum() == L.ambient_stratum()

    Equivalently in Q(2,-1^6)::

        sage: vt = VeeringTriangulation("(0,~6,7)(1,8,4)(2,~4,5)(3,~5,6)", "RRRRBBBBB")
        sage: L = vt.linear_subvariety()
        sage: L.multiscale_compactification() # optional - surface_dynamics  # not tested (folded edge)
        MultiscaleCompactification of Irreducible real linear subvariety of projective dimension 4 in [[Q_0(2, -1^6)]] made of
        5 components in codimension 1
        11 components in codimension 2
        13 components in codimension 3
        6 components in codimension 4

    A meromorphic example H(2,-2)::

        sage: vt = VeeringTriangulation("(0:1,1:1,~0:1,~1:1)", "RB")
        sage: L = vt.linear_subvariety()
        sage: L.multiscale_compactification()
        MultiscaleCompactification of Irreducible real linear subvariety of projective dimension 1 in [[H_1(2, -2)]] made of
        2 components in codimension 1
    """
    def __init__(self, L):
        self._L = L
        self._degeneration_helper = PrimeDegenerations()

        # at position (i, j) = i vertical and j horizontal degenerations
        self._components = collections.defaultdict(set)
        self._components[0, 0].add(L)
        d = L.projective_dimension()

        # vertical degenerations
        for codim in range(d):
            for comp in self._components[codim, 0]:
                for comp_deg in comp.codimension_one_vertical_degenerations(degeneration_helper=self._degeneration_helper):
                    self._components[codim + 1, 0].add(comp_deg)
            if not self._components[codim + 1, 0]:
                # NOTE: sometimes full vertical degeneration are not possible, eg H(2)
                break

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

    # TODO: in the literature these are called "strata" rather than "components"
    def components(self, *args):
        r"""
        Return components of this multiscale compactification.

        With no argument, return all components.  With a single argument
        ``codimension``, returns the list of components with the given
        codimension. With two arguemtns ``vertical_codimension``,
        ``horizontal_codimension`` return the list of components with the given
        vertical and horizontal components.

        EXAMPLES::

            sage: from veerer import VeeringTriangulation
            sage: vt = VeeringTriangulation("(0,6,~5)(~0,~4,5)(1,8,~7)(~1,~8,3)(2,7,~6)(~2,~3,4)", "RRRBBBBBB")
            sage: L = vt.linear_subvariety()
            sage: M = L.multiscale_compactification()
            sage: len(M.components())
            12
            sage: sorted(M.components(1))  # optional - surface_dynamics
            [Irreducible real linear subvariety of projective dimension 2 in [[H_1(0)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(2, -1^2)]],
             Irreducible real linear subvariety of projective dimension 2 in [[H_1(0^2)], [H_0(2, -2^2)]]]
            sage: sorted(M.components(2))  # optional - surface_dynamics
            [Irreducible real linear subvariety of projective dimension 1 in [[H_0(0, -1^2)], [H_1(2, -2)]],
             Irreducible real linear subvariety of projective dimension 1 in [[H_0(0^2, -1^2)], [H_0(2, -2^2)]],
             Irreducible real linear subvariety of projective dimension 1 in [[H_0(2, -1^4)]],
             Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(0^2, -2)], [H_0(2, -2^2)]],
             Irreducible real linear subvariety of projective dimension 1 in [[H_1(0)], [H_0(2, -1^2, -2)]]]
            sage: M.components(2, 1)  # optional - surface_dynamics
            [Irreducible real linear subvariety of projective dimension 0 in [[H_0(0, -1^2)], [H_0(0^2, -2)], [H_0(2, -2^2)]]]
            sage: M.components(3, 0)  # optional - surface_dynamics
            []
        """
        ans = []
        if len(args) == 0:
            for comps in self._components.values():
                ans.extend(comps)
        elif len(args) == 1:
            codim, = args
            if not isinstance(codim, numbers.Integral) or codim < 0 or codim > self._L.projective_dimension():
                raise ValueError("invalid codimension")
            ans = []
            for i in range(codim + 1):
                j = codim - i
                if (i, j) in self._components:
                    ans.extend(self._components[i, j])
        elif len(args) == 2:
            vert_codim, horiz_codim = args
            if not isinstance(vert_codim, numbers.Integral) or not isinstance(horiz_codim, numbers.Integral) or vert_codim < 0 or horiz_codim < 0 or vert_codim + horiz_codim > self._L.projective_dimension():
                raise ValueError("invalid codimensions")
            ans.extend(self._components[vert_codim, horiz_codim])
        else:
            raise ValueError("invalid specification of codimension")

        return ans

    def __repr__(self):
        if self.projective_dimension() == 0:
            return "MultiscaleCompactification {}".format(self._L)
        s = ["MultiscaleCompactification of {} made of".format(self._L)]
        for codim in range(1, self.projective_dimension() + 1):
            s.append("{} components in codimension {}".format(len(self.components(codim)), codim))
        return "\n".join(s)
