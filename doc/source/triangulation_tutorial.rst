.. -*- coding: utf-8 -*-
.. linkall

Embedded graphs and triangulations
==================================

Cell decomposition of surfaces
------------------------------

All topological surfaces in veerer are encoded as two permutations: one for the
vertices and one for the faces which are often denoted ``vp`` and ``fp`` in the
code. More precisely, each surface is represented by a cell decomposition and
each edge of this decomposition is given an index between ``0`` and ``ne - 1``
where ``ne`` is the number of edges. A *dart* is a choice of a vertex, an
adjacent edge and an adjacent face in this cell decomposition. It is in
bijection with oriented edges and the two darts associated to the edge ``i``
are encoded with the indices ``2i`` (canonical orientation) and ``2i+1``
(reversed orientation). When using strings, the darts writes ``i`` and ``~i``.
Now following the counter-clockwise order around vertices or faces give rise to
two permutations of the darts. The most basic class to handle such data
structure is :class:`~veerer.constellation.Constellation` which has many
derived classes

* :class:`~veerer.triangulation.Triangulation`: for triangulation of surfaces that we present in this section

* :class:`~veerer.veering_triangulation.VeeringTriangulation`: TODO make ref to section

* :class:`~veerer.strebel_graph.StrebelGraph`: TODO make ref to section

Building triangulations
-----------------------

In the following example we use the class
:class:`~veerer.triangulation.Triangulation` to build a sphere and a torus made
of two triangles each. The constructor only needs the permutation corresponding
to the faces

::

    sage: from veerer import Triangulation
    sage: sphere = Triangulation("(0,1,2)(~0,~2,~1)")
    sage: torus = Triangulation("(0,1,2)(~0,~1,~2)")

To recover the permutation of darts one can use the methods
:func:`~veerer.constellation.Constellation.vertex_permutation` and
:func:`~veerer.constellation.Constellation.face_permutation`

::

    sage: sphere.vertex_permutation()
    array('i', [5, 2, 1, 4, 3, 0])
    sage: sphere.face_permutation()
    array('i', [2, 5, 4, 1, 0, 3])

Note that veerer uses arrays (from the standard Python library `array
<https://docs.python.org/fr/3.13/library/array.html>`_) to represent
permutations. These behave similarly to the more standard lists but can only
contain integer values.

There are many functions to recover topological informations

::

    sage: sphere.euler_characteristic()
    2
    sage: sphere.is_connected()
    True
    sage: sphere.automorphisms()
    [array('i', [0, 1, 2, 3, 4, 5]),
     array('i', [1, 0, 5, 4, 3, 2]),
     array('i', [4, 5, 0, 1, 2, 3]),
     array('i', [3, 2, 1, 0, 5, 4]),
     array('i', [2, 3, 4, 5, 0, 1]),
     array('i', [5, 4, 3, 2, 1, 0])]

    sage: torus.euler_characteristic()
    0
    sage: torus.is_connected()
    True

Here an automorphism is an automorphism of the cell decomposition. In terms of
permutations, it is simply the intersection of the centralizer of the vertex
permutation and the centralizer of the face permutation.

Relabelling and isomorphism classes of triangulations
-----------------------------------------------------

When dealing with triangulations of surfaces an important task is to be able to
distinguish when two triangulations are isomorphic (under relabelling of their
darts). For example, alternative labellings of the sphere we considered in the
previous section are given by

::

    sage: sphere2 = Triangulation("(0,2,1)(~0,~1,~2)")
    sage: sphere3 = Triangulation("(0,~1,~2)(~0,2,1)")
    sage: sphere.is_isomorphic(sphere2)
    True
    sage: sphere.is_isomorphic(sphere3)
    True

The function :meth:`~veerer.constellation.Constellation.is_isomorphic` also detects
that our ``sphere`` and ``torus`` are not isomorphic

::

    sage: sphere.is_isomorphic(torus)
    False

One can apply a relabelling to a given triangulation using
:meth:`~veerer.constellation.Constellation.relabel`. Though the triangulation
it is applied to must be mutable

::

    sage: mutable_sphere = sphere.copy(mutable=True)
    sage: mutable_sphere.relabel("(0,~2)(~0,2)")
    sage: mutable_sphere
    Triangulation("(0,~1,2)(~0,~2,1)")

By default, triangulations are constructed as immutable. Trying to relabel an
immutable triangulation will result in an error

::

    sage: sphere.relabel("(0,~2)(~0,2)")
    Traceback (most recent call last):
    ...
    ValueError: immutable triangulation; use a mutable copy instead

The function :meth:`~veerer.constellation.Constellation.is_isomorphic` can be
called with an additional argument that provides a relabelling when the two
triangulations are isomorphic

::

    sage: sphere2.is_isomorphic(sphere3, certificate=True)
    (True, array('i', [0, 1, 5, 4, 3, 2]))
    sage: sphere2_mutable = sphere2.copy(mutable=True)
    sage: sphere2_mutable.relabel([0, 1, 5, 4, 3, 2])
    sage: sphere2_mutable == sphere3
    True

When handling a set of isomorphism classes, it is convenient to use a canonical
representative of the isomorphism class. In veerer these are called *canonical labels*.

::

    sage: mutable_sphere.set_canonical_labels()
    sage: mutable_sphere
    Triangulation("(0,1,2)(~0,~2,~1)")
    sage: mutable_sphere2.set_canonical_labels()
    sage: mutable_sphere2
    Triangulation("(0,1,2)(~0,~2,~1)")

Similarly to :func:`~veerer.constellation.Constellation.is_isomorphic` the
function :func:`~veerer.constellation.Constellation.set_canonical_labels` has
an optional argument ``mapping`` which makes the function return the array used
to turn the triangulation to its canonical version.

Boundaries and folded edges
---------------------------

The :class:`~veerer.triangulation.Triangulation` that we presented can actually
handle a bit more structure. Namely it is allowed to have a *boundary* (faces of
the cell decomposition that are not necessarily triangles) and folded
edges (edge glued to themselves).

A folded edge is represented by a dart ``i`` for which the opposite dart ``~i``
is not part of the face permutation

::

    sage: sphere_with_folded_edges = Triangulation("(0,1,2)")
    sage: sphere_with_folded_edges.face_permutation()
    array('i', [2, -1, 4, -1, 0, -1])

Note that veerer uses partial permutations here: the darts ``~0``, ``~1`` and
``~2`` encoded by ``1``, ``3`` and ``5`` are mapped to ``-1`` in the array. These
``-1`` in a permutation means "not part of the domain" and can be used to detect
folded edges.

Each dart carries a non-negative integer weight which by default is 0. If
positive, the corresponding half-edge is considered as a boundary. In a face, either
all edges must have weight 0 and the face must be a triangle (internal face) or
all edges must have positive weight. Here is an example of a disk which is made
of two triangles and its boundary is a quadrilateral

::

    sage: disk = Triangulation("(0,1,2)(~0,3,4)(~2:2,~1:1,~4:1,~3:1)")
    sage: disk.triangles()
    [[0, 2, 4], [1, 6, 8]]
    sage: disk.boundary_faces()
    [[3, 9, 7, 5]]

Notice that dart weights are specified using colons in the face permutation.
