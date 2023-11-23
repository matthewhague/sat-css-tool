"""dimacsWrapperFull.py

This is an adaptation of Z3py wrapper for Z3 but to instead output a file
in a DIMACS format.

Returns a fmla object, which is a list of clauses asserting v <=> fmla
where v is a variable that is true iff the whole formula is true
"""

from subprocess import Popen, PIPE

import sys

__variableCounter__ = 0 # Number of boolean variables
memo = {} # keep track of variables that are defined

# Here you have to add your solvers and the relative path to the solvers
# (this module will call that solver from the shell)
__solverDict__ = {"glucose": ["./glucose", "-model"], \
        "glucose-parallel": ["./glucose-parallel"],\
        "lingeling": ["lingeling"],\
        "plingeling": ["plingeling"],\
        "lingeling-druplig": ["lingeling-druplig"],\
        "riss": ["./riss"],\
        "glucoser": ["./glucoser_static"]
        }

__DEBUG__ = False

sat = True
unsat = False

def Bool(varName):
    if __DEBUG__:
        print('Bool: ' + varName)

    global __variableCounter__
    global memo
    # If varName was defined
    if varName in memo:
        var = memo[varName]
        return _Fmla(var, [])

    # If varname was not defined
    __variableCounter__ += 1 # Increase the counter
    memo[varName] = __variableCounter__ # The first variable is indexed 1

    var = memo[varName]
    return _Fmla(var, [])

def human_readable(fmla):
    """
    :param fmla:
        A formula built using And, Or, Not, &c.
    :returns:
        The list of clauses with variable names replacing numbers
    """
    #global memo
    #names = { i : n for (n, i) in memo.iteritems() }
    #return [ [ names[i] if i > 0 else "!" + names[-i]
    #           for i in clause ]
    #         for clause in fmla ]
    return [] # TODO

def Or(*vartuple):
    # In the case when there's only one argument
    if len(vartuple) == 0:
        var = _get_fresh_var()
        return _Fmla(var, [[-var]])
    elif len(vartuple) == 1 and isinstance(vartuple[0], _Fmla):
        return vartuple[0]

    # make vartuple the list of all clauses
    if len(vartuple) == 1 and isinstance(vartuple[0], list):
        vartuple = vartuple[0]

    # when there are multiple arguments
    var = _get_fresh_var()

    clauses = []
    for arg in vartuple:
        clauses.extend(arg.clauses)
    options = [ arg.var if not arg.negated else -arg.var
                for arg in vartuple ]

    clauses.append([-var] + options)
    for lit in options:
        clauses.append([-lit, var])

    return _Fmla(var, clauses)

def Not(arg):
    return _Fmla(arg.var, arg.clauses, not arg.negated)

def And(*vartuple):
    # In the case when there's only one argument
    if len(vartuple) == 0:
        var = _get_fresh_var()
        return _Fmla(var, [[var]])
    elif len(vartuple) == 1 and isinstance(vartuple[0], _Fmla):
        return vartuple[0]

    # make vartuple the list of all clauses
    if len(vartuple) == 1 and isinstance(vartuple[0], list):
        vartuple = vartuple[0]

    var = _get_fresh_var()
    clauses = []

    for arg in vartuple:
        clauses.extend(arg.clauses)
    requirements = [ arg.var if not arg.negated else -arg.var
                     for arg in vartuple ]

    first_clause = [ -lit for lit in requirements ]
    first_clause.append(var)
    clauses.append(first_clause)

    for lit in requirements:
        clauses.append([-var, lit])

    res = _Fmla(var, clauses)
    return res

def Implies(f1, f2):
    var = _get_fresh_var()
    clauses = f1.clauses + f2.clauses
    f1v = f1.var if not f1.negated else -f1.var
    f2v = f2.var if not f2.negated else -f2.var
    # var => -f1.var or f2.var
    clauses.append([-var, -f1v, f2v])
    # -f1.var => var
    clauses.append([f1v, var])
    # f2.var => var
    clauses.append([-f2v, var])

    return _Fmla(var, clauses)

def is_true(val):
    return val


class Solver(object):
    """Wrapper for solver outputting DIMACS CNF format"""

    def __init__(self,solver = ""):
        if solver == "":
            from main import get_commandline_solver
            self.__solver__ = get_commandline_solver()
        else:
            self.__solver__ = solver
        self.reset()

    def reset(self):
        # This has to be fixed to undefine
        self.__formula__ = [[]]
        self.__model_lines = []

    def getSolverName(self):
        return self.__solver__

    def add(self,fmla):
        assert isinstance (fmla, _Fmla), "not _Fmla passed to add"
        end = len(self.__formula__) - 1
        self.__formula__[end].append(fmla)

    def push(self):
        self.__formula__.append([])

    def pop(self):
        self.__formula__.pop()

    def set(self, prop, value):
        # TODO: set timeout
        pass

    def check(self):
        assert hasattr(self,'__formula__'), "Solver: check: formula was not"+\
                                            "yet added"
        print("Starting", self.__solver__)
        cmd = __solverDict__[self.__solver__]
        proc = Popen(cmd, stdout=PIPE, stdin=PIPE)
        self.__print_formula(proc.stdin)

        self.__model_lines = []
        for line in proc.stdout:
            if "UNSATISFIABLE" in line:
                return unsat
            elif "SATISFIABLE" in line:
                get_model = True
            elif 'v' == line[0]:
                self.__model_lines.append(line[1:].strip())

        return sat

    def model(self):
        global __variableCounter__

        if len(self.__model_lines) == 0:
            return None
        else:
            model = dict()
            for line in self.__model_lines:
                assignments = dict()
                for lit in line.split(' '):
                    val = int(lit)
                    if val < 0:
                        assignments[-val] = False
                    else:
                        assignments[val] = True
            model = dict()
            for i in range(__variableCounter__ + 1):
                if i in assignments:
                    model[_Fmla(i, [])] = assignments[i]
                else:
                    model[_Fmla(i, [])] = False
            return model

    def __print_formula(self, fout):
        # Opening: p cnf VARIABLES CLAUSES
        num_clauses = 0
        for level in self.__formula__:
            for fmla in level:
                num_clauses += 1 + len(fmla.clauses)

        fout.write('p cnf ' + str(__variableCounter__) + ' ' + \
                   str(num_clauses) + '\n')

        for level in self.__formula__:
            for fmla in level:
                if fmla.negated:
                    fout.write(str(-fmla.var))
                else:
                    fout.write(str(fmla.var))

                fout.write(' 0\n')

                for clause in fmla.clauses:
                    for varIndex in clause:
                        fout.write(str(varIndex))
                        fout.write(' ')
                    fout.write('0\n')
                fout.flush()
        fout.close()


def _get_fresh_var():
    global __variableCounter__
    __variableCounter__ += 1
    var = __variableCounter__
    return var

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

