.. -*- coding: utf-8 -*-
.. linkall

veerer: flat surfaces with veering triangulations
=================================================

Veerer is a package for `SageMath <https://www.sagemath.org>`_ to deal with
veering triangulations of surfaces and their associated flat structures. It
is part of the
`sage-flatsurf suite <https://flatsurf.github.io/sage-flatsurf>`_. Veerer
can in particular be used

* to provide canonical representatives of pseudo-Anosov homeomorphisms
  of surfaces. In particular, it allows to solve the conjugacy in the
  mapping class group for pseudo-Anosov mapping classes.

* to compute a decomposition of real linear subvarieties in finitely
  many cells (veerer could be used in particular to certify them) and
  enumerate pseudo-Anosov mapping classes that are supported on them

* to compute the multiscale compactification of a given real linear
  subvariety

The theoretical background of veering triangulation and L-infinity Delaunay
triangulations is based on ideas of I. Agol and F. Guéritaud, and is developed
in [BeDeGaGuSc]_, [Zy]_ and [FuDeZy]_.

Installation
------------

To install veerer on your computer, we refer to the `installation section of
sage-flatsurf <https://flatsurf.github.io/sage-flatsurf>`_.

Tutorials
---------

.. toctree::
   :maxdepth: 1
   :caption: Contents:

   background
   triangulation_tutorial
   veerer_demo
   ferenczi_zamboni
   references

Module documentation
--------------------

.. toctree::
   :maxdepth: 2

   automaton
   constants
   constellation
   delaunay_cone
   delaunay_strebel_graph
   features
   flat_structure
   flatsurf_conversion
   flip_sequence
   framing_group
   labelled_digraph
   layout
   linear_family
   linear_subvariety
   misc
   monodromy
   multiscale_veering_triangulation
   permutation
   strebel_graph
   tatami_decomposition
   triangulation
   veering_quadrangulation
   veering_triangulation
