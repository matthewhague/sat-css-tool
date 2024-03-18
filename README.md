# SatCSS

Minimise CSS files through semantics-preserving refactoring.  E.g.

    .a { color: red }
    .b { color: red }

can be refactored

    .a, .b { color: red }

but

    .a { color: red }
    .c { color: blue }
    .b { color: red }

cannot, since

    .a, .b { color: red }
    .c { color: blue }

changes the color of an element with class="b c".

Can also be used to test whether two selectors may match the same node in some DOM.

Can also be used as a tool/library for building an abstract
representation of a CSS file as a set of pairs (selector, declaration)
with an ordering (representing the order selectors must appear in the
CSS file to maintain the overriding semantics).

## Research

This repository is an example implementation of a rule-merging algorithm, which is
further explained in [CSS Minification via Constraint Solving][toplas]

## Requirements:

Python 3.7 or compatible.

* [cssselect 1.2.0](https://pypi.python.org/pypi/cssselect)
* [docopt 0.6.2](https://pypi.python.org/pypi/docopt)
* [lxml 4.9.2](https://pypi.python.org/pypi/lxml)
* [tinycss2 1.2.1](https://pypi.python.org/pypi/tinycss2)
* [toposort 1.10](https://pypi.org/project/toposort/)
* [z3-solver 4.12.2.0](http://research.microsoft.com/en-us/um/redmond/projects/z3/z3.html)

Borrowed and modified code from

* [cssselect 0.9.1](https://pypi.python.org/pypi/cssselect)

The recommended build system is [Poetry](https://python-poetry.org/). Tested
with version 1.7.0.

## External Requirements

In the same directory as satcss/main.py, ensure that running 

    ./z3

runs the Z3 SMT solver.  For example, this can be a symlink to the
Z3 installed on your machine.  

The tool was last tested with Z3 v4.12.2.0.

## Running with Poetry

To setup and run the project with Poetry, from the root directory run

    poetry install

Then

    poetry run satcss --help

To try a benchmark:

    poetry run satcss benchmarks/dblp-2015-07-09-stripmq.css

To output the file:

    poetry run satcss -o --file=blah.min.css benchmarks/dblp-2015-07-09-stripmq.css

## Running without Poetry

Two scripts `main.py` and `test.py` are provided in the root directory for
running without Poetry. First install the requirements manually. You can use
`requirements.txt`.

    pip install -r requirements.txt

Then run

    python main.py --help

where "python" is your python 3.7 or above command.

## TOPLAS Version

The version current as of the [TOPLAS paper][toplas] is tagged
[TOPLAS-Release][toplasrelease].

[toplas]: https://dl.acm.org/doi/10.1145/3310337
[toplasrelease]: https://github.com/matthewhague/sat-css-tool/releases/tag/TOPLAS-Release
