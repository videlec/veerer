.. -*- coding: utf-8 -*-
.. linkall
.. _veering-triangulation-and-strebel-graph-tutorial:

Veering triangulations and Strebel graphs
=========================================

In the :ref:`section on triangulation <triangulation-tutorial>` we explained
how triangulations are encoded in veerer. Our goal is now to explain how
veering triangulations and Strebel graphs can be built and used to parametrize
quadratic differentials on Riemann surfaces.

A veering triangulation is a triangulation together with a colouring of its
edges in either blue (``"B"``) or red (``"R"``) such that there is neither
monochromatic face nor monochromatic vertex.

TODO: use LaTeX math symbolis where relevant!

Each veering triangulation parametrizes a family of quadratic differentials.
More precisely, we consider coordinates that turn the given topological
triangulation into a flat triangulation in such way that each red edge
has a positive and each blue edge has a negative slope. This set of
quadratic differentials is parametrized by pairs of coordinates
on edges ``x_e`` and ``y_e`` subject to the following conditions

* variables ``x_e`` and ``y_e`` are positive

* for each face ``x_e`` and ``y_e`` satisfies the triangular
  equality

Building veering triangulation
------------------------------

The torus example from :ref:`section on triangulation <triangulation-tutorial>` have six
associated colouring that are veering

::

    sage: from veerer import Triangulation, VeeringTriangulation
    sage: torus = Triangulation("(0,1,2)(~0,~1,~2)")
    sage: coloured_torus0 = VeeringTriangulation(torus, "BBR")
    sage: coloured_torus1 = VeeringTriangulation(torus, "BRB")
    sage: coloured_torus2 = VeeringTriangulation(torus, "RBB")
    sage: coloured_torus3 = VeeringTriangulation(torus, "RRB")
    sage: coloured_torus4 = VeeringTriangulation(torus, "RBR")
    sage: coloured_torus5 = VeeringTriangulation(torus, "BRR")

Though, there are only two isomorphism classes

::

    sage: coloured_torus0.is_isomorphic(coloured_torus1)
    True
    sage: coloured_torus0.is_isomorphic(coloured_torus2)
    True

This fact can also be checked by looking at their canonical labellings

::

    sage: coloured_tori = [coloured_torus0, coloured_torus1, coloured_torus2,
    ....:  coloured_torus3, coloured_torus4, coloured_torus5]
    sage: for vt in coloured_tori:
    ....:     vt_copy = vt.copy(mutable=True)
    ....:     vt_copy.set_canonical_labels()
    ....:     print(vt_copy)
    VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBB")
    VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBB")
    VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RBB")
    VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
    VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")
    VeeringTriangulation("(0,1,2)(~0,~1,~2)", "RRB")

It can be checked that the sphere example from the :ref:`section on triangulation
<triangulation-tutorial>` have no red, blue colouring which is veering.

Quadratic differentials
-----------------------

The edge coordinates are constrained by linear equations and hence form a cone. These
can be obtained as follows

::

    sage: from veerer import VERTICAL, HORIZONTAL
    sage: Cx = coloured_torus0.cone(VERTICAL)
    sage: Cy = coloured_torus0.cone(HORIZONTAL)
    sage: Cx.rays()
    [[1, 0, 1], [1, 1, 0]]
    sage: Cy.rays()
    [[1, 1, 0], [0, 1, 1]]

The cones ``Cx`` and ``Cy`` obtained above have a custom type from ``veerer``
:class:`~veerer.polyhedron.cone.Cone`. It behaves similarly to the polyhedron
in sage except that

* it only handle homgeneous cones

* it does not compute the V-representation at construction (ie rays)
