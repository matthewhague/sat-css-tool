"""Integers represented as booleans in binary or unary format -- because BitVec isn't
working for some reason.

Note: only comparisons with constants implemented.

Provides Z3BinInt, Z3UnaryIntGT, and Z3UnaryIntEq.

Example usage:

    s = Solver()
    # construct var that represents 0..99
    v = Z3UnaryIntGT('name', 100)
    for c in v.get_variable_constraints():
        s.add(c)
    s.add(v == 4)

Z3BinInt is an encoding where the number is stored in variables as binary.

Z3UnaryIntGT is an encoding where the formula is linear in the maxint, where the
ith var means the value is >= i.

Z3UnaryIntEq is an encoding where the formula is quadratic in the maxint, where the
ith var means the value is == i.

Note: encodings require variable_contraint() to be asserted in the solver.
"""

from math import ceil, log

import z3

class Z3IntException(Exception):
    pass

class Z3BinInt:

    def __init__(self, name, maxint, z3wrapper = z3):
        """Construct a representation of a positive integer with z3 booleans.
           Add self.variable_constraint() to your formula to ensure correct
           encoding (not actually needed for boolean, but added for consistency
           with other encodings below).

           Note: equality/hashing is by name only (having multiple with same
           name will cause Z3 confusion)

        :param name:
            String name of var
        :param maxint:
            the maximum integer value (i.e. 0..maxint-1)
        :param z3wrapper:
            use this z3 module instead of the default (default: z3)
        """
        self._z3 = z3wrapper

        nbits = max(1,int(ceil(log(maxint, 2))))

        self._bvars = [ self._z3.Bool(name + "(" + str(i) + ")")
                        for i in range(nbits) ]

        self._maxint = maxint
        self._name = name

        # Memoize for speedity
        self._ltmemo = dict()
        self._gtmemo = dict()
        self._eqmemo = dict()

    def get_value(self, model):
        """
        :param model:
            A Z3 model
        :returns:
            The value of the integer given the values assigned in model
        """
        n = 0
        bval = 1
        for v in self._bvars:
            if self._z3.is_true(model[v]):
                n += bval
            bval *= 2
        return n

    def is_even(self):
        """:returns: Formula asserting val is even"""
        return self._z3.Not(self._bvars[0])

    def get_variable_constraints(self):
        return [self < self._maxint]

    def get_hashable_handle(self):
        """Because __eq__ is overridden for z3 purposes, we cannot hash a
        Z3BinInt, hence return a unique object to be used in place of self in
        hashmaps.  I.e. mymap[z3binint.get_hashable_handle()] = blah.

        :returns:
            A handle to use to represent the integer in hashmaps
        """
        return self._name

    def __int_to_bitvec(self, i):
        """
        :param i:
            an integer
        :returns:
            A vector of characters '0', '1' representing int, lsb first
        """
        return ('{0:0' + str(len(self._bvars)) + 'b}').format(i)[::-1]

    def __eq__(self, other):
        def do_eq():
            if isinstance(other, int):
                if other >= self._maxint:
                    return self._z3.Or()
                elif other < 0:
                    return self._z3.Or()
                else:
                    obits = self.__int_to_bitvec(other)
                    return self._z3.And([self._bvars[j] if obits[j] == '1'
                                                        else self._z3.Not(self._bvars[j])
                                         for j in range(len(self._bvars))])
            elif isinstance(other, Z3BinInt):
                # Use assume always 1 bit
                cons = [ self._bvars[0] == other._bvars[0] ]
                for j in range(1, max(len(self._bvars), len(other._bvars))):
                    if j >= len(self._bvars):
                        cons.append(self._z3.Not(other._bvars[j]))
                    elif j >= len(other._bvars):
                        cons.append(self._z3.Not(self._bvars[j]))
                    else:
                        cons.append(self._bvars[j] == other._bvars[j])
                return self._z3.And(cons)
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3BinInt with " + str(other.__class__))
        if self.__in_memo(self._eqmemo, other):
            return self.__get_from_memo(self._eqmemo, other)
        else:
            fmla = do_eq()
            self.__add_to_memo(self._eqmemo, other, fmla)
            return fmla

    def __ne__(self, other):
        return self._z3.Not(self == other)

    def __lt__(self, other):
        def do_lt():
            if isinstance(other, int):
                real_max = pow(2, len(self._bvars))
                if other >= real_max:
                    return self._z3.And()
                elif other <= 0:
                    return self._z3.Or()
                else:
                    # lt[j] will mean lt up to jth lsb
                    obits = self.__int_to_bitvec(other)
                    lt = []
                    if obits[0] == '1':
                        lt.append(self._z3.Not(self._bvars[0]))
                    else:
                        # can't be less than 0
                        lt.append(self._z3.Or())

                    for j in range(1, len(self._bvars)):
                        if obits[j] == '1':
                            lt.append(self._z3.Or(# same here and lt below
                                                  self._z3.And(self._bvars[j], lt[j-1]),
                                                  # lt here
                                                  self._z3.Not(self._bvars[j])))
                        if obits[j] == '0':
                            lt.append(# same here and lt below
                                      self._z3.And(self._z3.Not(self._bvars[j]),
                                                   lt[j-1]))

                    return lt[-1]
            elif isinstance(other, Z3BinInt):
                # Use assume always 1 bit
                lt = [ self._z3.And(self._z3.Not(self._bvars[0]), other._bvars[0]) ]
                for j in range(1, max(len(self._bvars), len(other._bvars))):
                    if j >= len(self._bvars):
                        lt.append(self._z3.Or(other._bvars[j], lt[j - 1]))
                    elif j >= len(other._bvars):
                        lt.append(self._z3.And(self._z3.Not(self._bvars[j]), lt[j - 1]))
                    else:
                        lt.append(self._z3.Or(self._z3.And(self._z3.Not(self._bvars[j]),
                                                           other._bvars[j]),
                                              self._z3.And(self._bvars[j] == other._bvars[j],
                                                           lt[j - 1])))
                return lt[-1]
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3BinInt with " + str(other.__class__))

        if self.__in_memo(self._ltmemo, other):
            return self.__get_from_memo(self._ltmemo, other)
        else:
            fmla = do_lt()
            self.__add_to_memo(self._ltmemo, other, fmla)
            return fmla

    def __le__(self, other):
        return self._z3.Not(self > other)

    def __gt__(self, other):
        def do_gt():
            if isinstance(other, int):
                real_max = pow(2, len(self._bvars))
                if other >= real_max - 1:
                    return self._z3.Or()
                elif other < 0:
                    return self._z3.And()
                else:
                    # gt[j] will mean gt up to jth lsb
                    obits = self.__int_to_bitvec(other)
                    gt = []
                    if obits[0] == '0':
                        gt.append(self._bvars[0])
                    else:
                        # can't be gt 1
                        gt.append(self._z3.Or())

                    for j in range(1, len(self._bvars)):
                        if obits[j] == '0':
                            gt.append(self._z3.Or(# same here and gt below
                                                  self._z3.And(self._z3.Not(self._bvars[j]),
                                                               gt[j-1]),
                                                  # gt here
                                                  self._z3.And(self._bvars[j])))
                        if obits[j] == '1':
                            gt.append(# same here and gt below
                                      self._z3.And(self._bvars[j], gt[j-1]))

                    return gt[-1]
            elif isinstance(other, Z3BinInt):
                gt = [ self._z3.And(self._bvars[0], self._z3.Not(other._bvars[0])) ]
                for j in range(1, max(len(self._bvars), len(other._bvars))):
                    if j >= len(self._bvars):
                        gt.append(self._z3.And(self._z3.Not(other._bvars[j]), gt[j - 1]))
                    elif j >= len(other._bvars):
                        gt.append(self._z3.Or(self._bvars[j], gt[j - 1]))
                    else:
                        gt.append(self._z3.Or(self._z3.And(self._bvars[j],
                                                           self._z3.Not(other._bvars[j])),
                                              self._z3.And(self._bvars[j] == other._bvars[j],
                                                           gt[j - 1])))
                return gt[-1]
            else:
                raise Z3IntException("Haven't implemented __gt__ for Z3BinInt with " + str(other.__class__))

        if self.__in_memo(self._gtmemo, other):
            return self.__get_from_memo(self._gtmemo, other)
        else:
            fmla = do_gt()
            self.__add_to_memo(self._gtmemo, other, fmla)
            return fmla

    def __ge__(self, other):
        return self._z3.Not(self < other)

    def __in_memo(self, memotable, item):
        """Helper function for checking in memo tables since Z3BinInt needs to
        use .get_hashable_handle() instead of the object itself.

        :param memotable:
            A dict
        :param item:
            The key to look for in the dict
        :returns:
            True iff item is in dict (or memotable[item.get_hashable_handle() if item
            is Z3BinInt)
        """
        if isinstance(item, Z3BinInt):
            return item.get_hashable_handle() in memotable
        else:
            return item in memotable

    def __get_from_memo(self, memotable, item):
        """Helper function for looking up in memo tables since Z3BinInt needs to
        use .get_hashable_handle() instead of the object itself.

        :param memotable:
            A dict
        :param item:
            The key to lookup in the dict
        :returns:
            The memotable[item] (or memotable[item.get_hashable_handle() if item
            is Z3BinInt)
        """
        if isinstance(item, Z3BinInt):
            return memotable[item.get_hashable_handle()]
        else:
            return memotable[item]

    def __add_to_memo(self, memotable, item, value):
        """Helper function for adding to memo tables since Z3BinInt needs to
        use .get_hashable_handle() instead of the object itself.

        :param memotable:
            A dict
        :param item:
            The key in the dict
        :param value:
            The value to associate to item (or item.get_hashable_handle() if
            item is Z3BinInt)
        """
        if isinstance(item, Z3BinInt):
            memotable[item.get_hashable_handle()] = value
        else:
            memotable[item] = value


class Z3UnaryIntGT:

    def __init__(self, name, maxint, z3wrapper = z3):
        """Construct a representation of a positive integer with z3 booleans.
           Note: must add self.get_variable_constraints() to the solver (they assert
           the integer only has one value).

           Uses an encoding where self._bvar[i] is true if the number is >= i as
           it has fewer constraints than asserting only one of the variables is
           true.

        :param name:
            String name of var
        :param nvals:
            The number of values in the boolean (0..maxint-1)
        :param z3wrapper:
            The z3 module to use (default z3)
        """
        self._z3 = z3wrapper

        self._bvars = [ self._z3.Bool(name + "(" + str(i) + ")")
                        for i in range(maxint) ]

        # Memoize for speedity
        self._ltmemo = dict()
        self._gtmemo = dict()
        self._eqmemo = dict()

        # is even function, only calculate if needed
        self._is_even = None

        self._variable_constraint = self._z3.And([ self._z3.Implies(self._bvars[i+1],
                                                                    self._bvars[i])
                                                   for i in range(len(self._bvars) - 1) ])

    def get_variable_constraints(self):
        """ :returns: list of Z3 expression that must be asserted for the integer
        representation to be valid"""
        return [self._variable_constraint]


    def get_value(self, model):
        """
        :param model:
            A Z3 model
        :returns:
            The value of the integer given the values assigned in model
        """
        for (i, v) in enumerate(self._bvars):
            if not self._z3.is_true(model[v]):
                return i - 1
        # if they're all true we're >= max value
        return len(self._bvars) - 1

    def is_even(self):
        """:returns: Formula asserting val is even"""
        maxint = len(self._bvars)
        if self._is_even is None:
            self._is_even = self._z3.Or([ self._z3.And(self._bvars[i],
                                                       self._z3.Not(self._bvars[i+1]))
                                          for i in range(0, maxint - 1, 2) ])
            # if las number is even (maxint - 1)
            if maxint % 2 == 1:
                self._is_even = self._z3.Or(self._is_even, self._bvars[maxint - 1])

        return self._is_even

    def __eq__(self, other):
        def do_eq():
            if isinstance(other, int):
                maxint = len(self._bvars) - 1
                if other > maxint:
                    return self._z3.Or()
                elif other == maxint:
                    return self._bvars[other]
                elif other < 0:
                    return self._z3.Or()
                else:
                    return self._z3.And(self._bvars[other],
                                        self._z3.Not(self._bvars[other+1]))
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3UnaryInt with " + str(other.__class__))
        if other in self._eqmemo:
            return self._eqmemo[other]
        else:
            fmla = do_eq()
            self._eqmemo[other] = fmla
            return fmla


    def __ne__(self, other):
        return self._z3.Not(self == other)

    def __lt__(self, other):
        def do_lt():
            if isinstance(other, int):
                if other >= len(self._bvars):
                    return self._z3.And()
                elif other < 0:
                    return self._z3.Or()
                else:
                    return self._z3.Not(self._bvars[other])
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3UnaryInt with " + str(other.__class__))

        if other in self._ltmemo:
            return self._ltmemo[other]
        else:
            fmla = do_lt()
            self._ltmemo[other] = fmla
            return fmla

    def __le__(self, other):
        return self._z3.Or(self < other, self == other)

    def __ge__(self, other):
        def do_gt():
            if isinstance(other, int):
                if other >= len(self._bvars):
                    return self._z3.Or()
                elif other < 0:
                    return self._z3.And()
                else:
                    return self._bvars[other]
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3UnaryInt with " + str(other.__class__))

        if other in self._gtmemo:
            return self._gtmemo[other]
        else:
            fmla = do_gt()
            self._gtmemo[other] = fmla
            return fmla

    def __gt__(self, other):
        return self._z3.And(self >= other, self != other)


class Z3UnaryIntEq:

    def __init__(self, name, maxint, z3wrapper = z3):
        """Construct a representation of a positive integer with z3 booleans.
           Note: must add self.get_variable_constraints() to the solver (they
           assert the integer only has one value).

           Uses an encoding where self._bvar[i] is true if the number is >= i as
           it has fewer constraints than asserting only one of the variables is
           true.

           Note: variable could actually be -1! (if all values are false)

        :param name:
            String name of var
        :param nvals:
            The number of values in the boolean (0..maxint-1)
        :param z3wrapper:
            The z3 module to use (default z3)
        """
        self._z3 = z3wrapper

        self._bvars = [ self._z3.Bool(name + "(" + str(i) + ")")
                       for i in range(maxint) ]

        # Memoize for speedity
        self._ltmemo = dict()
        self._gtmemo = dict()
        self._eqmemo = dict()

        # is even function, only calculate if needed
        self._is_even = None

        self._variable_constraint = self.__construct_variable_constraint()

    def get_variable_constraints(self):
        """ :returns: list of Z3 expression that must be asserted for the integer
        representation to be valid"""
        return [self._variable_constraint]


    def get_value(self, model):
        """
        :param model:
            A Z3 model
        :returns:
            The value of the integer given the values assigned in model
        """
        for (i, v) in enumerate(self._bvars):
            if self._z3.is_true(model[v]):
                return i
        raise Z3IntException("Z3UnaryInt.get_value() found no value in the given model.")

    def is_even(self):
        """:returns: Formula asserting val is even"""
        maxint = len(self._bvars)
        if self._is_even is None:
            self._is_even = self._z3.Or([ self._z3.And(self._bvars[i], self._z3.Not(self._bvars[i+1]))
                                 for i in range(0, maxint - 1, 2) ])
            # if las number is even (maxint - 1)
            if maxint % 2 == 1:
                self._is_even = self._z3.Or(self._is_even, self._bvars[maxint - 1])

        return self._is_even

    def __construct_variable_constraint(self):
        """:returns: a constraint asserting only one of self._bvars is true at
        any one time"""
        maxint = len(self._bvars) - 1

        if maxint == 0:
            return self._bvars[0]

        all_false_lte = [ self._z3.Not(self._bvars[0]) ]
        for i in range(1, maxint + 1):
            all_false_lte.append(self._z3.And(self._z3.Not(self._bvars[i]),
                                     all_false_lte[-1]))

        all_false_gte = [ self._z3.Not(self._bvars[maxint]) ]
        for i in range(maxint - 1, -1, -1):
            all_false_gte.append(self._z3.And(self._z3.Not(self._bvars[i]),
                                     all_false_gte[-1]))
        all_false_gte = all_false_gte[::-1]

        cons = [ self._z3.And(self._bvars[0], all_false_gte[1]) ]
        for i in range(1, maxint - 1):
            cons.append(self._z3.And(all_false_lte[i-1],
                            self._bvars[i],
                            all_false_gte[i+1]))
        cons.append(self._z3.And(all_false_lte[maxint - 1],
                        self._bvars[maxint]))

        return self._z3.Or(cons)


    def __eq__(self, other):
        def do_eq():
            if isinstance(other, int):
                maxint = len(self._bvars) - 1
                if other > maxint:
                    return self._z3.Or()
                elif other == maxint:
                    return self._bvars[other]
                elif other < 0:
                    return self._z3.Or()
                else:
                    return self._z3.And(self._bvars[other],
                               self._z3.Not(self._bvars[other+1]))
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3UnaryInt with " + str(other.__class__))
        if other in self._eqmemo:
            return self._eqmemo[other]
        else:
            fmla = do_eq()
            self._eqmemo[other] = fmla
            return fmla


    def __ne__(self, other):
        return self._z3.Not(self == other)

    def __lt__(self, other):
        def do_lt():
            if isinstance(other, int):
                if other >= len(self._bvars):
                    return self._z3.And()
                elif other <= 0:
                    return self._z3.Or()
                else:
                    return self._z3.Or(self._bvars[:other])
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3UnaryInt with " + str(other.__class__))

        if other in self._ltmemo:
            return self._ltmemo[other]
        else:
            fmla = do_lt()
            self._ltmemo[other] = fmla
            return fmla

    def __le__(self, other):
        return self._z3.Or(self < other, self == other)

    def __ge__(self, other):
        def do_gt():
            if isinstance(other, int):
                if other >= len(self._bvars):
                    return self._z3.Or()
                elif other < 0:
                    return self._z3.And()
                else:
                    return self._z3.Or(self._bvars[other:])
            else:
                raise Z3IntException("Haven't implemented __lt__ for Z3UnaryInt with " + str(other.__class__))

        if other in self._gtmemo:
            return self._gtmemo[other]
        else:
            fmla = do_gt()
            self._gtmemo[other] = fmla
            return fmla

    def __gt__(self, other):
        return self._z3.And(self >= other, self != other)

