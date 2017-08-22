"""wcnfWrapperFull.py

This is an adaptation of Z3py wrapper for Z3 but to instead output a file
in a DIMACS-wcnf format (for weighted partial max-sat solvers). See

http://maxsat.ia.udl.cat/requirements/

for the format.

Returns a fmla object, which is a list of clauses asserting v <=> fmla
where v is a variable that is true iff the whole formula is true
"""

from subprocess import Popen, PIPE
from tempfile import mkstemp
from os import fdopen

import sys
import signal

__variableCounter__ = 0 # Number of boolean variables
memo = {} # keep track of variables that are defined

OUTPUT_AND_EXIT="output_and_exit"

# Here you have to add your solvers and the relative path to the solvers
# (this module will call that solver from the shell)
# name maps to tuple (solver_executable, input_via_stdin)
# if input_via_stdin is false, a file (mktemp) will be used (hopefully this is
# in RAM)
__solverDict__ = {
    "open-wbo": ("./open-wbo_static", True),
    "maxhs": ("./maxhs", False),
    "z3-dimacs": (["./z3", "-dimacs", "-in"], True),
    "eva500a": (["./eva500a__"], True),
    "eva500a-via-tmp": ("./eva500a__", False),
    "qmaxsat14": ("./qmaxsat14.04auto-glucose3_static", True),
    OUTPUT_AND_EXIT: (None, False)
}

__DEBUG__ = False

sat = True
unsat = False
top = 1 # maximum value

def Bool(varName):
    if __DEBUG__:
        print 'Bool: ' + varName

    global __variableCounter__
    global memo
    # If varName was defined
    if varName in memo:
        var = memo[varName]
        return _Lit(memo[varName])

    # If varname was not defined
    __variableCounter__ += 1 # Increase the counter
    memo[varName] = __variableCounter__ # The first variable is indexed 1

    return _Lit(memo[varName])

def Or(*vartuple):
    # In the case when there's only one argument
    assert len(vartuple) > 0, 'Or function should have at least one argument'

    if len(vartuple) == 1:
        if isinstance(vartuple[0], _Lit):
            return _Clause([vartuple[0]])
        if isinstance(vartuple[0], list):
            assert all([ el.__class__.__name__ == '_Lit' \
                    for el in vartuple[0]]), 'Input list contains non-literals'

            return _Clause(vartuple[0])

    clause = _Clause([])
    for arg in vartuple:
        if arg.__class__.__name__ == '_Lit':
            clause.add_lit(arg)
        elif arg.__class__.__name__ == '_Clause':
            clause.join(arg)
        else:
            assert False, 'Invalid argument to Or'

    return clause

def Not(arg):
    assert arg.__class__.__name__ == '_Lit', 'arg should be a literal'
    newLit = _Lit(arg.var,not arg.negated)
    return newLit # I'm not sure if we should just try not
                  # to create a new object here

def is_true(value):
    """
    :param value:
        The value from model[var] to test if is a true value
    :returns:
        True iff the value is the internal representation of true
    """
    return value

def is_false(value):
    """
    :param value:
        The value from model[var] to test if is a false value
    :returns:
        True iff the value is the internal representation of false
    """
    return not value

class Optimize(object):
    """Wrapper for solver outputting DIMACS WCNF format"""

    def __init__(self,solver = ""):
        if solver == "":
            from main import get_dimacs_output
            if get_dimacs_output():
                self.__solver__ = OUTPUT_AND_EXIT
            else:
                from main import get_commandline_solver
                self.__solver__ = get_commandline_solver()
        else:
            self.__solver__ = solver
        self.reset()

    def reset(self):
        # This has to be fixed to undefine
        self.__formula__ = [[]]
        self.__model_lines = []
        self.__opt_found__ = False

    def getSolverName(self):
        return self.__solver__

    def add(self,fmla):
        if isinstance(fmla,_Lit):
            clause = _Clause([fmla])
        elif isinstance(fmla,_Clause):
            clause = fmla
        else:
            assert False, "not _Lit or _Clause passed to add"
        self.__formula__[-1].append(clause)

    def add_soft(self,fmla,wt):
        # wt = weight
        if isinstance(fmla,_Lit):
            clause = _Clause([fmla])
        elif isinstance(fmla,_Clause):
            clause = fmla
        else:
            assert False, "not _Lit or _Clause passed to add"
        global top
        top += wt # update the maximum value (sum of all soft clauses)
        clause.set_weight(wt)
        self.__formula__[-1].append(clause)

        return _OptimizeHandle(self)

    def push(self):
        self.__formula__.append([])

    def pop(self):
        self.__formula__.pop()

    def set(self, prop, value):
        # TODO: set timeout
        pass

    def check(self, child_collector = None):
        """child_collector ignored"""
        assert hasattr(self,'__formula__'), "Solver: check: formula was not"+\
                                            "yet added"
        print "Starting", self.__solver__
        cmd, via_stdin = __solverDict__[self.__solver__]

        if via_stdin:
            proc = Popen(cmd, stdout=PIPE, stdin=PIPE)
            self.__print_formula(proc.stdin)
        else:
            fh, name = mkstemp()
            f = fdopen(fh, "w")
            self.__print_formula(f)
            f.close()
            full_cmd = [cmd, name]
            print full_cmd

            if self.__solver__ == OUTPUT_AND_EXIT:
                print "Dimacs written to", name
                print "Returning unsat"
                return unsat

            proc = Popen(full_cmd, stdout=PIPE)
            print "file written is", name, "remember to delete (left undeleted while in still unstable)"

        def kill_proc(arg1, arg2):
            proc.kill()
            exit()

        old_handler = signal.signal(signal.SIGTERM, kill_proc)

        self.__model_lines = []
        for line in proc.stdout:
            line = line.strip()
            # LINES FROM STANDARD SOLVER
            if "UNSATISFIABLE" in line:
                return unsat
            elif "OPTIMUM FOUND" in line:
                get_model = True
            elif "UNKNOWN" in line:
                assert False, 'Solver returns UNKNOWN, not handled'
                # Future work
            elif 'o' == line[0]:
                self.__opt_found__ = True
                self.__opt__ = int(line[2:])
            elif 'v' == line[0]:
                self.__model_lines.append(line[1:])
            # LINES FROM Z3
            elif "unsat" == line:
                return unsat
            elif "sat" == line:
                get_model = True
            elif line[0] == "1" or line[:2] == "-1":
                self.__model_lines.append(line)

        signal.signal(signal.SIGTERM, old_handler)

        return sat

    def value(self):
        assert self.__opt_found__ == True, 'Optimum was not found'
        return self.__opt__

    def model(self):
        global __variableCounter__

        if len(self.__model_lines) == 0:
            return {}
        else:
            model = dict()
            for line in self.__model_lines:
                assignments = dict()
                for lit in line.split(' '):
                    if len(lit) == 0:
                        continue

                    val = int(lit)
                    if val < 0:
                        assignments[-val] = False
                    else:
                        assignments[val] = True
            model = dict()
            for i in xrange(__variableCounter__ + 1):
                if i in assignments:
                    model[_Lit(i)] = assignments[i]
                else:
                    model[_Lit(i)] = False
            return model

    def __print_formula(self, fout):
        # Opening: p cnf VARIABLES CLAUSES
        num_clauses = 0
        for level in self.__formula__:
            for fmla in level:
                num_clauses += int( len(fmla) > 0 )

        if __DEBUG__:
            print 'p wcnf ' + str(__variableCounter__) + ' ' + \
                   str(num_clauses) + ' ' + str(top) + '\n'

        fout.write('p wcnf ' + str(__variableCounter__) + ' ' + \
                   str(num_clauses) + ' ' + str(top) + '\n')

        for level in self.__formula__:
            for clause in level:
                if clause.is_empty():
                    continue
                if clause.is_weighted():
                    out = str(clause.get_weight()) + ' ' # soft clause
                else:
                    out = str(top) + ' ' # hard clause

                out += str(clause)
                fout.write(out)
                fout.write(' 0\n')
                if __DEBUG__:
                    print out + ' 0'
                fout.flush()
        fout.close()

def _get_fresh_var():
    global __variableCounter__
    __variableCounter__ += 1
    var = __variableCounter__
    return var

class _Var:
    """Simple representation of a variable"""
    def __init__(self, var):
        """
        :param var:
            var is Variable name
        """
        self.var = var

    def __str__(self):
        return str(self.var)

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __eq__(self,other):
        if other.__class__.__name__ != "_Var":
            return False

        return self.var == other.var

    def __hash__(self):
        return hash(self.var)

class _Lit:
    """Simple representation of a literal"""
    def __init__(self,var,negated = False):
        self.var = _Var(var)
        self.negated = negated

    def negate(self):
        self.negated = not self.negated

    def __str__(self):
        if self.negated:
            s = '-'
        else:
            s = ''

        return s + str(self.var)

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __eq__(self,other):
        if other.__class__.__name__ != '_Lit':
            return 'False'

        return (self.var == other.var) & \
               (self.negated == other.negated)

    def __hash__(self):
        return hash(self.var) + hash(self.negated)

class _Clause:
    """Simple representation of a (weighted) clause"""
    def __init__(self, literals):
        """
        :param literals:
            A set of _Lit objects (literals)
        """
        if __DEBUG__:
            isinstance(literals,list)
            assert all([ el.__class__.__name__ == '_Lit' \
                    for el in literals]), '_Clause only take literals'

        self.literals = literals
        self.weight_set = False

    def set_weight(self,wt):
        assert isinstance(wt,int) and wt > 0, 'wt should be positive int'
        self.weight = wt
        self.weight_set = True

    def get_weight(self):
        assert self.weight_set, 'Weight was not set'
        return self.weight

    def add_lit(self,literal):
        """Add a literal"""
        assert literal.__class__.__name__ == '_Lit', "literal is not _Lit"
        self.literals.append(literal)

    def is_weighted(self):
        return self.weight_set

    def is_empty(self):
        if len(self.literals) == 0:
            return True
        else:
            return False

    def join(self,clause):
        """Add the literals in clause to self"""
        assert literal.__class__.__name__ == '_Clause', "clause is not _Clause"
        self.literals.extend(clause.literals)

    def __len__(self):
        return len(self.literals)

    def __str__(self):
        return ' '.join([ str(lit) for lit in self.literals])

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __eq__(self,other):
        if other.__class__.__name__ != '_Clause':
            return 'False'

        if len(self.literals) != len(other.literals):
            return 'False'

        return all([ l1 == l2 for (l1,l2) in \
                    zip(self.literals,other.literals)])

    def __hash__(self):
        return sum([hash(lit) for lit in self.literals])
        # Should this be product instead?

class _OptimizeHandle:
    """Optimize Handle"""
    def __init__(self,optimizer):
        assert isinstance(optimizer,Optimize), '_OptimizeHandle ' +\
                            'should be initialised with an Optimize obj'
        self.optimizer = optimizer

    def value(self):
        return self.optimizer.value()

class _Fmla:
    """Simple representation of a formula"""
    def __init__(self, var, clauses, negated = False):
        """
        :param var:
            A variable that will be true iff the formula is true, represented as an integer
        :param clauses:
            A list of list of integers representing clauses over the formulas
        :param negated:
            True if the formula should be negated
        """
        self.var = var
        self.clauses = clauses
        self.negated = negated

    def __str__(self):
        lines = [str(self.var) if not self.negated else str(-self.var)]
        for clause in self.clauses:
            lines.append(str(clause))
        return "\n".join(lines)

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __eq__(self, other):
        if other.__class__.__name__ != "_Fmla":
            return False

        return (self.var == other.var) & \
               (self.negated == other.negated)
               # we don't check clauses on the assumption that we never assigned
               # two sets of clauses to the same variable

    def __hash__(self):
        return hash(self.var) + hash(self.negated)
        # we don't check clauses on the assumption that we never assigned
        # two sets of clauses to the same variable

def main():
    x = Bool('x')
    y = Bool('y')
    opt = Optimize('open-wbo')
    opt.add(Or(x,y))
    print type(Not(x))
    opt.add_soft(x,3)
    h = opt.add_soft(x,2)
    opt.add_soft(y,5)
    opt.add_soft(Not(y),6)
    opt.check()
    print opt.model()
    print opt.value()

if __name__ == '__main__':
    main()
