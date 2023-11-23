"""Functions for tying conj/disj to variables and a class for handling integers
in a CNF encoding"""

from math import ceil, log

import z3


CNFINT_TRUEFALSE_VAR = "cnfint(true)(false)"

class CNFLibException(Exception):
    pass

def cnf_v_iff_conj(v, conjs, optimizer, z3wrapper = z3):
    """Helper function for tying variables to clauses.  Adds to optimizer CNF
    clauses representing

        v <=> conjs[0] & ... & conjs[n]

    :param v:
        A Z3 Variable
    :conjs:
        A list of Z3 Variables
    :param optimizer:
        A Z3 Solver/Optimize to add clauses to
    :param z3wrapper:
        The z3 module to use
    """
    not_v = z3wrapper.Not(v)

    # v => conjs[0] & ... & conjs[n]
    for c in conjs:
        optimizer.add(z3wrapper.Or(not_v, c))

    # conjs[0] & ... & conjs[n] => v
    clause = list(map(z3wrapper.Not, conjs))
    clause.append(v)
    optimizer.add(z3wrapper.Or(clause))



def cnf_v_iff_disj(v, disjs, optimizer, z3wrapper = z3):
    """Helper function for tying variables to clauses.  Adds to optimizer CNF
    clauses representing

        v <=> disjs[0] or ... or disjs[n]

    :param v:
        A Z3 Variable
    :disjs:
        A list of Z3 Variables
    :param optimizer:
        A Z3 Solver/Optimize to add clauses to
    :param z3:
        The z3 module to use
    """
    # v => disjs[0] or ... or disjs[n]
    clause = list(disjs)
    clause.append(z3wrapper.Not(v))
    optimizer.add(z3wrapper.Or(clause))

    # disjs[0] & ... & disjs[n] => v
    for c in disjs:
        optimizer.add(z3wrapper.Or(z3wrapper.Not(c), v))


class _BitSequence:
    """A class for representing common prefixes of bit sequences used by CNFInt
    without having to create new lists."""

    def __init__(self, bits, i, v):
        """A representation of the sequence

            v, bits[i+1..]

        :param bits:
            A sequence of bits in char format '0' or '1'
        :param i:
            An index in range(len(bits))
        :param v:
            A char '0' or '1'
        """
        self._bits = bits
        self._i = i
        self._v = v

        self._hash = (hash(i) +
                      hash(v) +
                      sum(hash(bits[j]) for j in range(i+1, len(bits))))

    def __str__(self):
        s = "".join(self._bits[j] for j in range(self._i+1, len(self._bits)))
        return s + v

    def __hash__(self):
        return self._hash

    def __eq__(self, other):
        if not isinstance(other, _BitSequence):
            return False

        if self._v != other._v or self._i != other._i or self._hash != other._hash:
            return False

        for j in range(self._i+1, len(self._bits)):
            if self._bits[j] != other._bits[j]:
                return False

        return True



class CNFInt:
    """A class for handling integers as binary, with methods for producing cnf
    encodings of integer comparisons with constants."""

    def __init__(self, name, maxint, z3wrapper = z3):
        """Construct a representation of a positive integer with z3 booleans.
           Add self.get_variable_constraints() to your formula to ensure correct
           encoding.

           Note: equality/hashing is by name only (having multiple with same
           name will cause Z3 confusion)

        :param name:
            String name of var
        :param maxint:
            the maximum integer value (i.e. 0..maxint-1).  If maxint is 0, maxint will be upped to 1.
        :param z3wrapper:
            use this z3 module instead of the default (default: z3)
        """
        self._z3 = z3wrapper

        self._maxint = max(maxint, 1)

        nbits = max(1,int(ceil(log(self._maxint, 2))))

        self._bvars = [ self._z3.Bool(name + "(" + str(i) + ")")
                        for i in range(nbits) ]

        self._name = name

        # Memoize for speedity
        self._ltmemo = dict()
        self._gtmemo = dict()
        self._eqmemo = dict()
        self._bitseqmemo = dict()
        self._lsbwithmemo = dict()

        self._true = self._z3.Bool(CNFINT_TRUEFALSE_VAR)
        self._false = self._z3.Not(self._true)

        # for generating new vars
        self._next_var = 0

        # variable constraints hold all constraints added to support cnf
        # encodings (must have constructed rest of self before calling <)
        self._variable_constraints = [ self._true ]
        self.__add_constraint(self < self._maxint)


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
        """:returns: Formula asserting val is even, of literal form Not(x)"""
        return self._z3.Not(self._bvars[0])

    def lsb_with(self, x):
        """
        :param x:
            An integer
        :return:
            a formula asserting that the bit sequence lsb first starts
            with bit encoding of x
        """
        def do_lsb_with():
            xbits = self.__int_to_bitvec(x)
            l = self.__get_fresh_var()

            # l => bit[0..i] = xbits
            for j in range(len(xbits)):
                if xbits[j] == '0':
                    self.__add_constraint(self._z3.Or(self._z3.Not(l),
                                                      self._z3.Not(self._bvars[j])))
                else: # '1'
                    self.__add_constraint(self._z3.Or(self._z3.Not(l),
                                                      self._bvars[j]))

            return l

        if self.__in_memo(self._lsbwithmemo, x):
            return self.__get_from_memo(self._lsbwithmemo, x)
        else:
            fmla = do_lsb_with()
            self.__add_to_memo(self._lsbwithmemo, x, fmla)
            return fmla


    def add_variable_contraints(self, optimizer):
        """ Adds a list of Or() clauses that need to be true for the
        encoding to work.

        :param optimizer:
            A Z3 optimizer to add the constraints to
        """
        gt0 = (self >= 0)
        ltmax = (self < self._maxint)

        for clause in self._variable_constraints:
            optimizer.add(clause)

    def get_variable_constraints(self):
        """:returns: A list of Z3 Or constraints that need to be asserted.
        NOTE: this may change as additional comparisions (e.g. x < 4) are made."""
        return self._variable_constraints

    def get_hashable_handle(self):
        """Because __eq__ is overridden for z3 purposes, we cannot hash a
        CNFInt, hence return a unique object to be used in place of self in
        hashmaps.  I.e. mymap[z3binint.get_hashable_handle()] = blah.

        :returns:
            A handle to use to represent the integer in hashmaps
        """
        return self._name

    def __get_fresh_var(self):
        """:returns: A fresh Bool variable"""
        x = self._z3.Bool(self._name + "_fresh_" + str(self._next_var))
        self._next_var += 1
        return x

    def __add_constraint(self, cons):
        """Adds new constraint to correctness of encoding

        :param cons:
            A Or() formula to assert about the bvars for correct encoding
        """
        self._variable_constraints.append(cons)

    def __int_to_bitvec(self, i):
        """
        :param i:
            an integer
        :returns:
            A vector of characters '0', '1' representing int, lsb first
        """
        return ('{0:0' + str(len(self._bvars)) + 'b}').format(i)[::-1]

    def __eq__(self, other):
        """Note: causes new constraints to be added to variable_contraints
        :param other:
            An integer constant
        :returns:
            A variable that is true iff self == other
        """
        def do_eq():
            if isinstance(other, int):
                real_max = pow(2, len(self._bvars))
                if other >= real_max or other < 0:
                    return self._false
                else:
                    obits = self.__int_to_bitvec(other)
                    lits = [ self._bvars[j] if obits[j] == '1'
                                            else self._z3.Not(self._bvars[j])
                             for j in range(len(self._bvars)) ]

                    v = self.__get_fresh_var()

                    for l in lits:
                        # v => l
                        self.__add_constraint(self._z3.Or(self._z3.Not(v), l))

                    # lits => v
                    if_dir = list(map(self._z3.Not, lits))
                    if_dir.append(v)
                    self.__add_constraint(self._z3.Or(if_dir))

                    return v
            else:
                raise CNFLibException("Haven't implemented __lt__ for Z3BinInt with " + str(other.__class__))

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
                    return self._true
                elif other <= 0:
                    return self._false
                else:
                    obits = self.__int_to_bitvec(other)
                    # will be an array of variables l for positions i where the
                    # integer might be equivalent from msb down to i+1, then lt
                    # at position i (that is '0' while obits[i] is '1').  The
                    # variable l will be true if the int is lt because of this
                    # position.  Not empty since 0000 invalid.
                    chances = []
                    for i in range(len(self._bvars)):
                        if obits[i] == '0':
                            continue
                        l = self.__is_bit_seq(obits, i, '0')
                        chances.append(l)

                    if len(chances) == 1:
                        return chances[0]
                    else:
                        v = self.__get_fresh_var()

                        # v <= Or(chances)
                        for l in chances:
                            self.__add_constraint(self._z3.Or(self._z3.Not(l),
                                                              v))
                        # v => Or(chances)
                        chances.append(self._z3.Not(v))
                        self.__add_constraint(self._z3.Or(chances))

                        return v
            else:
                raise CNFLibException("Haven't implemented __lt__ for Z3BinInt with " + str(other.__class__))

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
                    return self._false
                elif other < 0:
                    return self._true
                else:
                    obits = self.__int_to_bitvec(other)
                    # will be an array of variables l for positions i where the
                    # integer might be equivalent from msb down to i+1, then gt
                    # at position i (that is '1' while obits[i] is '0').  The
                    # variable l will be true if the int is gt because of this
                    # position.  Not empty since 1111 invalid.
                    chances = []
                    for i in range(len(self._bvars)):
                        if obits[i] == '1':
                            continue

                        l = self.__is_bit_seq(obits, i, '1')
                        chances.append(l)

                    if len(chances) == 1:
                        return chances[0]
                    else:
                        v = self.__get_fresh_var()

                        # v <= Or(chances)
                        for l in chances:
                            self.__add_constraint(self._z3.Or(self._z3.Not(l),
                                                              v))
                        # v => Or(chances)
                        chances.append(self._z3.Not(v))
                        self.__add_constraint(self._z3.Or(chances))

                        return v
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


    def __is_bit_seq(self, bits, i, v):
        """Note: can call to self.__add_constraint

        :param bits:
            A sequence of bits in char format '0' or '1'
        :param i:
            An index in range(len(bits))
        :param v:
            A char '0' or '1'
        :returns:
            A variable asserting that the integer matches the sequence

                v, bits[i+1..]

            for the most significant bits
        """

        bit_seq = _BitSequence(bits, i, v)
        if bit_seq in self._bitseqmemo:
            return self._bitseqmemo[bit_seq]
        else:
            l = self.__get_fresh_var()

            # l => bit[i+1..] = obit[i+1..] and bit[i] = v
            for j in range(i+1, len(self._bvars)):
                if bits[j] == '0':
                    self.__add_constraint(self._z3.Or(self._z3.Not(l),
                                                      self._z3.Not(self._bvars[j])))
                else: # '1'
                    self.__add_constraint(self._z3.Or(self._z3.Not(l),
                                                      self._bvars[j]))
            if v == '0':
                self.__add_constraint(self._z3.Or(self._z3.Not(l),
                                                  self._z3.Not(self._bvars[i])))
            else: # '1'
                self.__add_constraint(self._z3.Or(self._z3.Not(l), self._bvars[i]))


            #  l <= bit[0..i-1] = obit[0..i-1] and bit[i] = v
            neg_lits = [ (self._z3.Not(self._bvars[j])
                              if bits[j] == '1'
                              else self._bvars[j])
                         for j in range(i+1, len(self._bvars)) ]
            if v == '0':
                neg_lits.append(self._bvars[i])
            else: # '1'
                neg_lits.append(self._z3.Not(self._bvars[i]))
            neg_lits.append(l)
            self.__add_constraint(self._z3.Or(neg_lits))

            self._bitseqmemo[bit_seq] = l

            return l


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
        if isinstance(item, CNFInt):
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
        if isinstance(item, CNFInt):
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
        if isinstance(item, CNFInt):
            memotable[item.get_hashable_handle()] = value
        else:
            memotable[item] = value


