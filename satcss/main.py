"""Sat-CSS: minimise CSS files by searching for space-saving refactorings.  Can also run in emptiness mode to check intersection of pairs of CSS selectors.

Usage:
  main.py [-efops] [<file>] [<num_rules>] [--split=<num_rules>] [--file=<output_file>] [--refactor=<technique>] [--anneal=<anneal_type>] [--num-threads=<num>] [--num-parts=<num>] [--intermediate-results=<dir>] [--dimacs-output] [--enumeration-output] [--dont-refactor] [--output-simple] [--write-compact] [--compact-only] [--unopt-emp] [--unlim-bicliques] [--no-bicliques] [--no-ordering]
  main.py (-h | --help)
  main.py --version

Options:
  -e --emptiness               Run in an interactive mode for checking emptiness of intersection -- reads two selectors on two lines of stdin, writes E on stdout if intersection is empty, N otherwise
  -f --full-exclusion          When searching for refactoring, allow all selectors/properties to be excluded from max bicliques, instead of just those in edge order
  -h --help                    Show this screen.
  -i --altminit                Use iterative altminimise (<num rules> is initial estimate of size)
  -o --output-model            Outputs a new minimised CSS file (use with --file to write to a file)
  -p --multi-props             Combines multiply defined properties into a single value (e.g. { background: red; background: white } becomes { background: red;white }
  -s --size-only               Only output calculated size of file in bytes
  --anneal=<anneal_type>       Use simulated annealing for deduct refactor, can be none (no annealing), good (only refactorings that decrease size), any (any refactoring) [default: none]
  --compact-only               Simply read in the file, and write it out again minified (use --file to write to a file)
  --dont-refactor              Do not do refactoring (can be used with --output-simple, but not with --dimacs-only)
  --dimacs-output              Do not do refactoring.  Simply output to tempfiles dimacs versions of the first refactoring search and quit.
  --enumeration-output         Output (Mi, F) enumeration of maximal bicliques and positions at which they're forbidden (use with -d)
  --file=<output_file>         If outputting model, output to the name file
  --intermediate-results <dir> Directory to save the css file after each refactoring in --deduct-refactor mode.  Creates directory if doesn't exist.  If not specified, then no results saved.
  --output-simple              Output simpleCSS model of css file
  --no-bicliques               Pose refactoring problem as simple MaxSAT with one variable per selector/property and without biclique optimisation
  --no-ordering                Do not compute an edge ordering (i.e. refactor without respecting edge order)
  --num-threads=<num>          Add this to specify multiple threads for deduct refactoring search (will try to guess a good number if not supplied)
  --num-parts=<num>            When set to n, each thread will search 1/n of the search space per iteration (covering the whole search space in n iterations) -- a higher number means a faster search, but possibly the best refactoring will not be found (will try to guess a good number if not supplied))
  --unopt-emp                  Use unoptimised emptiness check that does a single large Presburger check
  --unlim-bicliques            Do not limit the number of orderable bicliques constructed from an unorderable one (by default all unorderable bicliques are simply ignored)
  --version                    Show the version.
  --write-compact              If outputting a model, write it compactly (minified)
"""

import sys

from docopt import docopt, DocoptExit
import importlib

import satcss.simplecssbuilder as simplecssbuilder
import satcss.cssfile as cssfile

from satcss.cliqueCSS import cliqueCSS
from satcss.deduct_refactor import AnnealType, refactor

ANNEAL_TYPES = { "none": AnnealType.none,
                 "good": AnnealType.good,
                 "any": AnnealType.any }
DEFAULT_ANNEAL = AnnealType.none

def get_output_file():
    """:returns: the output file specified on the command line, or None"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--file']
    except DocoptExit:
        return None

def get_anneal():
    """
    :returns:
        AnnealType determined by argument
    """
    try:
        arguments = docopt(__doc__, version='v0.1')
        return ANNEAL_TYPES[arguments['--anneal']]
    except DocoptExit:
        return DEFAULT_ANNEAL

def get_num_threads():
    """
    :returns:
        Num threads specified by --num-threads or None
    """
    try:
        arguments = docopt(__doc__, version='v0.1')
        val = arguments['--num-threads']
        if val is not None:
            return int(val)
    except DocoptExit:
        pass
    return None

def get_num_parts():
    """
    :returns:
        Num space divisions per thread or None
    """
    try:
        arguments = docopt(__doc__, version='v0.1')
        val = arguments['--num-parts']
        if val is not None:
            return int(val)
    except DocoptExit:
        pass
    return None

def get_intermediates_directory():
    """
    :returns:
        String given to --intermediate-results or None if not given
    """
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--intermediate-results']
    except DocoptExit:
        return DEFAULT_ANNEAL

def get_full_exclusion():
    """
    :returns:
        True iff the user specified that --full-exclusion
    """
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--full-exclusion']
    except DocoptExit:
        return False

# NOTE: implementation of this switch is hacky.  Look for instances of
# get_dimacs_output() scattered through code before assuming anything about
# it...
def get_dimacs_output():
    """:returns: the output file specified on the command line, or None"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--dimacs-output']
    except DocoptExit:
        return False

def get_enumeration_output():
    """:returns: whether --enumeration-output was specified on the command line"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--enumeration-output']
    except DocoptExit:
        return False

def get_dont_refactor():
    """:returns: whether --dont-refactor was specified on the command line"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--dont-refactor']
    except DocoptExit:
        return False

def get_output_simple():
    """:returns: whether --output-simple was specified on the command line"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--output-simple']
    except DocoptExit:
        return False

def get_no_bicliques():
    """:returns: whether --no-bicliques was specified on the command line"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--no-bicliques']
    except DocoptExit:
        return False

def get_no_ordering():
    """:returns: whether --no-bicliques was specified on the command line"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--no-ordering']
    except DocoptExit:
        return False

def get_unopt_emp():
    """
    :returns:
        True iff the user specified that --unopt-emp
    """
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--unopt-emp']
    except DocoptExit:
        return False

def get_unlim_bicliques():
    """
    :returns:
        True iff the user specified that --unlim-bicliques
    """
    try:
        arguments = docopt(__doc__, version='v0.1')
        return arguments['--unlim-bicliques']
    except DocoptExit:
        return False

def _do_model_output(model):
    """Outputs cliqueCSS model to stdout or file depending on cmdline"""
    try:
        arguments = docopt(__doc__, version='v0.1')
        if arguments['--output-model']:
            filename = get_output_file()
            if filename is None:
                if arguments['--write-compact']:
                    model.write_compact(sys.stdout)
                else:
                    print(model)
            else:
                fout = open(filename, 'w')
                if arguments['--write-compact']:
                    model.write_compact(fout)
                else:
                    print(model, file=fout)
                fout.close()
                print("Model output to", filename)
    except DocoptExit:
        pass

def refactor_file(arguments):
    css = cssfile.fromfile(arguments['<file>'],
                           arguments['--multi-props'])
    model = refactor(css)
    _do_model_output(model)

def emptiness_mode():
    """Runs in a loop, reading two selectors from stdin (on two lines), and
    writing E to stdout if the selectors do not overlap, N otherwise"""

    while True:
        try:
            sel1 = sys.stdin.readline()
            if sel1 == "":
                break
            if sel1.strip() == ".":
                sys.stdout.flush()
                continue
            sel2 = sys.stdin.readline()
            if sel2 == "":
                break

            if simplecssbuilder.selectors_overlap_str(sel1, sel2):
                sys.stdout.write("N")
            else:
                sys.stdout.write("E")
        except EOFError:
            break

def write_compact(arguments):
    """Read in file and output it in compacted form"""
    css = cssfile.fromfile(arguments['<file>'],
                           arguments['--multi-props'])
    clique = simplecssbuilder.cliquefromcssfile(css)

    filename = get_output_file()
    if filename is not None:
        fout = open(filename, 'w')
        clique.write_compact(fout)
        fout.close()
    else:
        clique.write_compact(sys.stdout)


def write_size(arguments):
    """Read in file and output calculated size"""
    css = cssfile.fromfile(arguments['<file>'],
                           arguments['--multi-props'])
    clique = simplecssbuilder.cliquefromcssfile(css)
    print("Calculated file size is", clique.size(), "bytes")

def main():
    importlib.reload(sys)
    arguments = docopt(__doc__, version='v0.1')

    if arguments['--emptiness']:
        emptiness_mode()
    else:
        if arguments['<file>'] is None:
            print("Please provide a file name! (see --help)")
            exit(-1)

        if arguments['--compact-only']:
            write_compact(arguments)
        elif arguments['--size-only']:
            write_size(arguments)
        else:
            refactor_file(arguments)

if __name__ == "__main__":
    main()
