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


## Requirements:

(Possibly a superset)

* [cssselect 0.9.1](https://pypi.python.org/pypi/cssselect)
* [docopt 0.6.2](https://pypi.python.org/pypi/docopt)
* [enum34](https://pypi.python.org/pypi/enum34)
* [lxml 3.4.4](https://pypi.python.org/pypi/lxml)
* [tinycss 0.3](https://pypi.python.org/pypi/tinycss)
* [z3](http://research.microsoft.com/en-us/um/redmond/projects/z3/z3.html)

Borrowed and modified code from

* [cssselect 0.9.1](https://pypi.python.org/pypi/cssselect)

## External Requirements

In the same directory as main.py, ensure that running 

    ./z3

runs the Z3 SMT solver.  For example, this can be a simlink to the
Z3 installed on your machine.  

The tool uses Z3 v4.5.  There have recently been changes to the Z3 API
for weighted Max-SAT.  Hence, the most up-to-date version as of
22/08/2017 is required.

## Running

    python main.py --help

where "python" is your python 2.7 command.

To try a benchmark:

    python main.py benchmarks/dblp-2015-07-09-stripmq.css

To output the file:

    python main.py -o --file=blah.min.css benchmarks/dblp-2015-07-09-stripmq.css 
