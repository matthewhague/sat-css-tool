"""A provision of the Z3Py interface that runs Z3 as a command line process
instead of the python-z3 api, to speed up formula construction, i hope...

Note: Only currently supports bools
"""

import abc
from subprocess import Popen, PIPE
import re
from string import maketrans
import sys
import os

from z3 import sat, unsat


_model_var_name_re = re.compile('.*\(define-fun (.*) \(\).*')
_model_var_name_group = 1

# set z3 path to same dir as this file
_Z3_PATH = os.path.join(os.path.dirname(os.path.realpath(__file__)), "z3")

_BOOL_TRUE = "true"
_BOOL_FALSE = "false"

# Convert everything to short names.  This avoids unrecognised characters in
# particular
_SHORT_NAMES = True

# Map from short names to long names
_name_table = dict()

# Next free short name
_next_short_name = 0

def _get_short_name(name):
    """
    :param name:
        String
    :returns:
        A new short name to use instead of name in fmla
    """
    global _next_short_name, _name_table
    short_name = 'x' + str(_next_short_name)
    _name_table[short_name] = name
    _next_short_name += 1
    return short_name

def _get_long_name(name):
    """
    :param name:
        A string short name
    :returns:
        A string that is the associated long name
    """
    global _name_table
    return _name_table[name]


class CmdZ3WrapperException(Exception):
    pass

class _Fmla(object):
    __metaclass__ = abc.ABCMeta

    @abc.abstractmethod
    def get_variables(self):
        """:returns: A dict of variable names (string) to z3 types (string) used
        in the formula"""
        pass

    @abc.abstractmethod
    def write(self, output):
        """Writes the fmla to the output

        :param output:
            something to write to with a write("string") method
        """
        pass


class _ParenFmla(_Fmla):
    """A representation of one Z3 parenthesis.  E.g. (and f1 f2 f3) or (+ 3
    4)"""

    def __init__(self, operator, empty, arguments):
        """
        :param operator:
            A string that is the operator of the parentheses
        :param empty:
            The string to write when arguments are empty.  E.g. or
            should be 'false'.  I.e. (or ) == false
        :param arguments:
            a tuple of arguments of type _Fmla, for which str(arguments[i]) gives the z3 input
            format representation (e.g. another _Fmla...).

            Can also be a single list, or omitted
        """
        # TODO handle lists of arguments or don't depending on whether ... is
        # bad for performance which i think i read it was.
        self._operator = operator
        self._empty = empty
        if len(arguments) == 1 and isinstance(arguments[0], list):
            self._arguments = arguments[0]
        else:
            self._arguments = arguments
        self._variables = { v : t
                            for argument in self._arguments
                                if isinstance(argument, _Fmla)
                            for (v, t) in argument.get_variables().iteritems() }

        for a in self._arguments:
            if a is None:
                raise CmdZ3WrapperException("None in arg list for " + operator)

    def get_variables(self):
        return self._variables

    def write(self, output):
        if len(self._arguments) == 0:
            output.write(self._empty)
        else:
            output.write('(')
            output.write(self._operator)
            for a in self._arguments:
                output.write(' ')
                if isinstance(a, _Fmla):
                    a.write(output)
                else:
                    output.write(str(a))
            output.write(')')

    def __str__(self):
        return "(" + self._operator + ' ' + ' '.join(str(a) for a in self._arguments) + ")"

class _BinFmla(_ParenFmla):
    """A representation of a binary z3 operator"""

    def __init__(self, operator, arg1, arg2):
        """
        :param operator:
            The operator as a string
        :param arg1:
            A _Fmla first argument
        :param arg2:
            A _Fmla first argument
        """
        super(_BinFmla, self).__init__(operator, "", (arg1, arg2))

class _UnFmla(_ParenFmla):
    """A representation of a unary z3 operator"""

    def __init__(self, operator, arg1):
        """
        :param operator:
            The operator as a string
        :param arg1:
            A _Fmla first argument
        """
        super(_UnFmla, self).__init__(operator, "", (arg1, ))


_trantable = maketrans('():,# "\'[]=\\|;/&', 'lrcChsqQLRebpSfA')

class _Variable(_Fmla):
    """A Z3 variable that needs declaring"""

    """A Z3 boolean can be used with"""
    __metaclass__ = abc.ABCMeta

    def __init__(self, name, the_type):
        """A boolean.  Note renames chars by _trantable, so careful of clashes!.

        :param name:
            A string giving the name of the variable
        :param the_type:
            A string giving the Z3 type of the variable (e.g. Bool)
        """
        if _SHORT_NAMES:
            self._name = _get_short_name(name)
        else:
            self._name = name.translate(_trantable)
        self._type = the_type
        self._variables = {self._name : self._type}

    def get_variables(self):
        return self._variables

    def write(self, output):
        output.write(self._name)

    def get_name(self):
        """:returns: the name of the variable"""
        return self._name

    def get_type(self):
        """:returns: the Z3 type as string"""
        return self._type

    @abc.abstractmethod
    def default_value(self):
        """
        :returns:
            A default value for the variable if not assigned by z3
        """
        pass

    def __str__(self):
        return self._name

    def __repr__(self):
        return repr(id(self)) + str(self)

    @abc.abstractmethod
    def __eq__(self, other):
        """
        :param other:
            Some z3 fmla or something
        :returns:
            A z3 formula asserting self == other
        """
        pass

    def __hash__(self):
        """Note: use a _DictableVariable when storing in a hashmap, this is
        provided here for lookup.  See __init__ comment of _DictableVariable."""
        return hash(self._name) + hash(self._type)

class Bool(_Variable):
    """A Z3 Boolean"""
    def __init__(self, name):
        """A boolean

        :param name:
            A string giving the name of the variable
        """
        super(Bool, self).__init__(name, "Bool")

    def default_value(self):
        return _BOOL_TRUE

    def __eq__(self, other):
        assert isinstance(other, Bool)
        return Eq(self, other)

class _ArithExpr(object):
    """Representation of Z3 arithmetic.  E.g. an integer variable x, or a sum (+
    x y)"""
    __metaclass__ = abc.ABCMeta

    def __eq__(self, other):
        return Eq(self, other)

    def __lt__(self, other):
        return Lt(self, other)

    def __gt__(self, other):
        return Gt(self, other)

    def __lte__(self, other):
        return Lte(self, other)

    def __gte__(self, other):
        return Gte(self, other)


class Int(_ArithExpr, _Variable):
    """A Z3 Integer"""
    def __init__(self, name):
        """A boolean

        :param name:
            A string giving the name of the variable
        """
        # If i understand correctly, this calls _Variable.__init__...
        super(_ArithExpr, self).__init__(name, "Int")

    def default_value(self):
        return 0

class And(_ParenFmla):
    def __init__(self, *arguments):
        super(And, self).__init__("and", _BOOL_TRUE, arguments)

class Or(_ParenFmla):
    def __init__(self, *arguments):
        super(Or, self).__init__("or", _BOOL_FALSE, arguments)

class Implies(_BinFmla):
    def __init__(self, arg1, arg2):
        super(Implies, self).__init__("implies", arg1, arg2)

class Iff(_BinFmla):
    def __init__(self, arg1, arg2):
        super(Iff, self).__init__("iff", arg1, arg2)

class Not(_UnFmla):
    def __init__(self, arg1):
        super(Not, self).__init__("not", arg1)

class Sum(_ParenFmla, _ArithExpr):
    """A Z3 (+ ...) fmla.  Caution, does not check types."""
    def __init__(self, *arguments):
        super(Sum, self).__init__("+", 0, arguments)

class Eq(_BinFmla):
    """Two Z3 ints are equal, caution does not assert types!"""
    def __init__(self, arg1, arg2):
        super(Eq, self).__init__("=", arg1, arg2)

class Lt(_BinFmla):
    """Two Z3 ints are equal, caution does not assert types!"""
    def __init__(self, arg1, arg2):
        super(Lt, self).__init__("<", arg1, arg2)

class Gt(_BinFmla):
    """Two Z3 ints are equal, caution does not assert types!"""
    def __init__(self, arg1, arg2):
        super(Gt, self).__init__(">", arg1, arg2)

class Lte(_BinFmla):
    """Two Z3 ints are equal, caution does not assert types!"""
    def __init__(self, arg1, arg2):
        super(Lte, self).__init__("<=", arg1, arg2)

class Gte(_BinFmla):
    """Two Z3 ints are equal, caution does not assert types!"""
    def __init__(self, arg1, arg2):
        super(Gte, self).__init__(">=", arg1, arg2)

class _Handle(object):
    """A soft constraint handle"""

    def __init__(self):
        self._value = 0

    def _set_value(self, value):
        """Assigns the value of the handle

        :param value:
            The value to assign to the handle
        """
        self._value = value

    def value(self):
        """:returns: the value of the handle after solve"""
        return self._value

class Model(object):
    """A Z3 model, use self[v] to lookup values of variables"""

    def __init__(self):
        self._lookup = dict()

    def set_value(self, varname, varval):
        """
        :param varname:
            String, variable name
        :param varval:
            Value of the variable as string
        """
        self._lookup[varname] = varval

    def __getitem__(self, key):
        assert isinstance(key, _Variable)
        name = key.get_name()
        if name not in self._lookup:
            return key.default_value()
        else:
            return self._lookup[name]

    def __str__(self):
        return str(self._lookup)

def is_true(value):
    """
    :param value:
        A value from model returned by solver
    :returns:
        True if value is true
    """
    return value == _BOOL_TRUE

def is_false(value):
    """
    :param value:
        A value from model returned by solver
    :returns:
        True if value is false
    """
    return value == _BOOL_FALSE


class _SolverFrame(object):
    """Holds internal solver details for a given frame"""

    def __init__(self, variables, handle = None):
        """Creates a blank frame where variables is the dict from variable names
        to types from the previous frame."""
        self._variables = {}
        self._variables.update(variables)
        self._hard_constraints = []
        self._soft_constraints = []
        self._handle = handle

    def get_hard_constraints(self):
        """:returns: the list of hard constraints"""
        return self._hard_constraints

    def get_soft_constraints(self):
        """:returns: the list of soft constraints (pairs of (fmla, weight))
                     where fmla is a _Fmla and weight an integer"""
        return self._soft_constraints

    def add(self, fmla):
        """Adds a hard constraint to the frame

        :param fmla:
            A _Fmla to add, or a list of _Fmla to add
        """
        if isinstance(fmla, list):
            for f in fmla:
                self._variables.update(f.get_variables())
                self._hard_constraints.append(f)
        else:
            self._variables.update(fmla.get_variables())
            self._hard_constraints.append(fmla)

    def add_soft(self, fmla, weight):
        """Adds a soft constraint with weight.

        :param fmla:
            A _Fmla to add
        :param weight:
            The cost of violating the constraint as integer
        :returns:
            The handle of the soft constraints
        """
        self._variables.update(fmla.get_variables())
        self._soft_constraints.append((fmla, weight))
        if self._handle is None:
            self._handle = _Handle()
        return self._handle


    def get_variables(self):
        """:returns: dict from variables (string) to variable types (string)
        used in frame and prev frames"""
        return self._variables

    def get_handle(self):
        """:returns: the handle for soft constraints (only one handle supported
        for weighted)"""
        return self._handle


class _Z3Solver(object):
    """Implements functions for both Solver and Optimize"""

    # TODO: push and pop

    def __init__(self, opt_prefix = ""):
        """
        :param opt_prefix:
            A string to prefix to option names in self.set
        """
        self._opt_prefix = opt_prefix
        # list of _SolverFrame
        self._frames = [_SolverFrame({})]
        # dict[optionname] = optionvalue (options set by user)
        self._options = dict()
        # if soft constraints, have a handle so they can get the weight of sat
        # assignment
        self._handle = None
        # dict[variablename] = value assigned in sat assignment
        self._model = Model()

    def push(self):
        """Push a new solver frame"""
        prevvars = self._frames[-1].get_variables()
        handle = self._frames[-1].get_handle()
        self._frames.append(_SolverFrame(prevvars, handle))

    def pop(self):
        """Pop latest from from solver"""
        self._frames.pop()

    def add(self, fmla):
        """Adds a hard constraint to the solver

        :param fmla:
            A _Fmla to add
        """
        self._frames[-1].add(fmla)

    def add_soft(self, fmla, weight):
        """Adds a soft constraint with weight.

        :param fmla:
            A _Fmla to add
        :param weight:
            The cost of violating the constraint as integer
        :returns:
            A handle to get the value of the satisfying assignment from after checking
        """
        return self._frames[-1].add_soft(fmla, weight)

    def set(self, opt, value):
        """Sets an option value.  E.g. set('timeout', 6000)

        :param opt:
            String option name
        :param value:
            Value as something for which str(value) works
        """
        self._options[self._opt_prefix + opt] = value

    def model(self):
        """:returns: The model as a Model.  .check() must be called first."""
        return self._model

    def check(self, child_collector = None):
        """Runs z3 on the constraints added.

        :param child_collector:
            a ChildCollector used in multi-threaded mode to allow started
            instances of z3 to be tracked and reliably terminated.  Or None
            if not being used.
        :returns:
            sat or unsat
        """
        if child_collector is not None:
            child_collector.get_create_child_lock()

        try:
            proc = Popen([_Z3_PATH, "-in"], stdout=PIPE, stdin=PIPE)
        except OSError:
            print "Error running Z3, did you make sure", _Z3_PATH, "exists?"
            exit(-1)

        if child_collector is not None:
            child_collector.add_new_child(proc)
            child_collector.release_create_child_lock()

        self.__print_problem(proc.stdin)
        # self.__print_problem(sys.stdout)

        # o = open("fmla.z3", "w")
        # self.__print_problem(o)
        # o.close()

        proc.stdin.close()
        res = self.__read_response(proc.stdout)

        return res

    def __print_problem(self, output):
        """Writes the z3 problem to z3.

        :param output:
            PIPE to write problem to.
        """
        # always output model if exists
#        output.write('(set-option :dump-models true)\n')

        for (opt, value) in self._options.iteritems():
            output.write('(set-option :')
            output.write(opt)
            output.write(' ')
            output.write(str(value))
            output.write(')\n')

        for (v, t) in self._frames[-1].get_variables().iteritems():
            output.write('(declare-fun ')
            output.write(v)
            output.write(' () ')
            output.write(t)
            output.write(')\n')

        for frame in self._frames:
            for fmla in frame.get_hard_constraints():
                output.write('(assert ')
                fmla.write(output)
                output.write(')\n')

        for frame in self._frames:
            for (fmla, weight) in frame.get_soft_constraints():
                output.write('(assert-soft ')
                fmla.write(output)
                output.write(' :weight ')
                output.write(str(weight))
                output.write(')\n')

        output.write('(check-sat)\n')
        output.write('(get-objectives)')
        output.write('(get-model)')

    def __read_response(self, inpipe):
        """Reads Z3's responses and record the results.

        :returns:
            sat or unsat
        """
        # Read result
        res = None
        resline = inpipe.readline().strip()
        if resline == "sat":
            res = sat
        elif resline == "unsat":
            res = unsat
        else:
            raise CmdZ3WrapperException("Could not decipher result '" +
                                        resline +
                                        "' from Z3.")

        # Read model
        self._model = Model()
        if res == sat:
            # Read optimize result if soft constraints
            handle = self._frames[-1].get_handle()
            # ignore (objectives
            inpipe.readline()
            if handle is not None:
                valline = inpipe.readline()
                # remove ()s from value and convert to int
                handle._set_value(int(valline.translate(None, '()')))
            # read trailing )
            inpipe.readline()

            # read (model
            inpipe.readline()

            # read rest of model
            line = inpipe.readline().strip()
            while line != ")":
                m = _model_var_name_re.match(line)
                if m is None:
                    raise CmdZ3WrapperException('Unexpected model line from z3: ' + line)
                varname = m.group(_model_var_name_group)

                line = inpipe.readline()
                varval = line.translate(None, ')\n ').strip()

                self._model.set_value(varname, varval)

                # start next loop
                line = inpipe.readline().strip()

        return res

class Solver(_Z3Solver):
    pass

class Optimize(_Z3Solver):
    def __init__(self):
        super(Optimize, self).__init__("opt.")
