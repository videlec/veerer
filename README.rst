Veerer
======

Veerer is a package for `SageMath <https://www.sagemath.org>`_ to deal with
veering triangulations of surfaces and their associated flat structures.
Veerer is based on SageMath and relies heavily on

* `Parma Polyhedra Library (ppl)
  <https://www.bugseng.com/content/parma-polyhedra-library>`_ and `Normaliz
  <https://www.normaliz.uni-osnabrueck.de/>`_ for polyhedral computations
  when computing with linear subvarieties

Links
-----

* documentation: https://flatsurf.github.io/veerer/

* Python Package Index page: https://pypi.org/project/veerer/

* development website: https://github.com/flatsurf/veerer/

Contributors
------------

* Mark Bell (Warwick)

* Vincent Delecroix (Bordeaux)

* Kai Fu (Bordeaux)

* Saul Schleimer (Warwick)

Testing
-------

To run the SageMath doctests, install the package with pip, typically::

    $ sage -pip install -e .

and then run::

    $ sage -t --force-lib veerer/

Or::

    $ sage -t --force-lib veerer/my_file.py

Building the documentation
--------------------------

Go to the ``docs`` directory and then do::

    $ make html

The documentation should be available under ``docs/build/`` as HTML pages.

Typically you might want to use ``veerer_demo.rst`` as a Jupyter notebook.
In order to convert ``veerer_demo.rst`` into ``veerer_demo.ipynb`` you need
to have available on your computer

- rst2latex python-docutils
- pdflatex
- pandoc
- the Python package rst2ipynb
- the Python package nbconvert

Then do::

    $ export FILE_PREFIX="veerer_demo"
    $ rst2ipynb --kernel=sagemath veerer_demo.rst veerer_demo.ipynb

If you installed rst2ipynb using the ``--user`` option of pip, the executables
might be installed in ``$HOME/.local/bin``, in which case you should first make
the system aware of this via::

    $ PATH=$PATH:$HOME/.local/bin

Authors
-------

- Mark Bell
- Vincent Delecroix
- Kai Fu
- Saul Schleimer
