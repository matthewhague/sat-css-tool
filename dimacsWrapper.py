"""dimacsWrapper.py

This is an adaptation of Z3py wrapper for Z3 but to instead output a file
in a DIMACS format.

NOTE: For this to work, minimise.py should only use boolean variables.
"""

from subprocess import call

__variableCounter__ = 0 # Number of boolean variables
memo = {} # keep track of variables that are defined

# Here you have to add your solvers and the relative path to the solvers
# (this module will call that solver from the shell)
__solverDict__ = {"glucose": "./glucose", \
        "glucose-parallel": "./glucose-parallel",\
        "lingeling": "lingeling",\
        "plingeling": "plingeling",\
        "lingeling-druplig": "lingeling-druplig",\
        "riss": "./riss",\
        "glucoser": "./glucoser_static"
        }

__outputFile__ = 'output.txt'

__DEBUG__ = False

sat = True

def Bool(varName):
    if __DEBUG__:
        print 'Bool: ' + varName

    global __variableCounter__
    global memo
    # If varName was defined
    if varName in memo:
        return memo[varName]

    # If varname was not defined
    __variableCounter__ += 1 # Increase the counter
    memo[varName] = __variableCounter__ # The first variable is indexed 1

    return memo[varName]

def human_readable(fmla):
    """
    :param fmla:
        A formula built using And, Or, Not, &c.
    :returns:
        The list of clauses with variable names replacing numbers
    """
    global memo
    names = { i : n for (n, i) in memo.iteritems() }
    return [ [ names[i] if i > 0 else "!" + names[-i]
               for i in clause ]
             for clause in fmla ]

def Or(arg1,*vartuple):
    # In the case when there's only on argument
    if len(vartuple) == 0:
        if isinstance(arg1,list):
            return arg1
        else:
            assert isinstance(arg1,int), "Or: first argument has to be an int"
            return [arg1]

    # when there are multiple arguments
    assert isinstance(arg1,int), "Or: first argument has to be an int"
    Clause = [arg1]
    for arg in vartuple:
        assert isinstance(arg1,int), "Or: subsequent arguments have to be ints"
        Clause.append(arg)

    return Clause

def Not(arg):
    assert isinstance(arg,int), "Not: argument has to be an int"
    return -arg

def And(clauseList):
    # We assume that the input is a list of clauses
    return clauseList

class Solver(object):
    """Wrapper for solver outputting DIMACS CNF format"""

    def __init__(self,solver = ""):
        if solver == "":
            from main import get_commandline_solver
            self.__solver__ = get_commandline_solver()
        else:
            self.__solver__ = solver

    def reset(self):
        # This has to be fixed to undefine
        __formula__ = []

    def getSolverName(self):
        return self.__solver__

    def add(self,cnfForm):
        """cnfForm is a list of list of numbers representing a boolean formula
        in CNF."""
        self.__formula__ = cnfForm

    def print_formula(self):
        fout = open(__outputFile__,'w')
        # Opening: p cnf VARIABLES CLAUSES
        fout.write('p cnf ' + str(__variableCounter__) + ' ' + \
                str(len(self.__formula__)) + '\n')

        #print the clauses
        assert hasattr(self,'__formula__'), "Solver: check: formula was not"+\
                                            "yet added"

        for clause in self.__formula__:
            if __DEBUG__:
                # printing the clause
                print 'print_formula: ' + clause

            clauseStr = [str(varIndex) for varIndex in clause]
            # e.g. clauseStr = ['7','-8'], then Tuple = ('','7 -8')
            String = ' '.join(clauseStr)
            # Ending the clause with 0 (clause separator for DIMACS)
            line = String + ' 0\n'
            fout.write(line)

        fout.close()

    def check(self):
        assert hasattr(self,'__formula__'), "Solver: check: formula was not"+\
                                            "yet added"
        self.print_formula()
        call([__solverDict__[self.__solver__],__outputFile__])

def main():
    print [ Or(Not(Bool('x')),Bool('y'),Bool('z'),Bool('z1')) ]

if __name__ == '__main__':
    main()
