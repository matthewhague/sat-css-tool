"""
A hack for constructing partial weighted max sat instances from wcnf files 
for z3.
Authors: Anthony Lin, Matt Hague
"""
import sys
from timeit import default_timer

from z3 import *

def construct_z3_optimizer(fin):
    """
    Construct a z3 optimizer from wcnf file referenced by fin
    """
    # Ignoring comments
    for line in fin:
        linestrip = line.strip()
        if len(linestrip) > 0 and linestrip[0] == 'c':
            continue
        elif len(linestrip) > 0 and linestrip[0] == 'p':
            break
        else:
            assert False, 'Parse error: p expected after comments'

    # Extracting p-info
    assert linestrip[0] == 'p', 'Empty file' # the only possibility of error
    if line[0] == ' ':
        line = linestrip
    line_array = line.split()
    assert len(line_array) == 5, 'Unexpected number of words in p line'
    assert line_array[0] == 'p'
    assert line_array[1] == 'wcnf'
    try:
        nbvar = int(line_array[2])
        assert nbvar >= 1, 'Non-positive number of variables'
        nbclauses = int(line_array[3])
        assert nbclauses >= 1, 'Non-positive number of clauses'
        top = int(line_array[4])
        assert top >= 1, 'Non-positive weight for hard constraints'
    except ValueError:
        assert False, 'Unexpected input'

    opt = Optimize()
    # Parsing clauses
    for line in fin:
        line_array = line.split()
        try:
            wt = int(line_array[0])
            Clause = []
            for lit in line_array[1:-1]: # Note last number is 0
                var = abs(int(lit))
                z3var = Bool(str(var))
                if int(lit) > 0:
                    Clause.append(z3var)
                elif int(lit) < 0:
                    Clause.append(Not(z3var))
                else:
                    assert False, 'Zero value is seen prematurely'
        except ValueError:
            assert False, 'Unexpected input'
        if wt == top:
            opt.add(Or(Clause))
        elif wt < top:
            h = opt.add_soft(Or(Clause),wt)
        else:
            assert False, 'Weight bigger than max weight declared'

    return (opt,h)

def main():
    filename = 'file.wcnf'
    if len(sys.argv) > 0:
        filename = sys.argv[1]
        print(sys.argv[1])

    fin = open(filename,'r')
    (opt,h) = construct_z3_optimizer(fin)

    opt.set('maxsat_engine', 'wmax')

    print("Checking...")
    start_t = default_timer()
    opt.check()
    end_t = default_timer()
    print("Done in", (end_t - start_t), "s")

    print(opt.model())
    print(h.value())

if __name__ == '__main__':
    main()
