
"""Functions for analysing the satisfiability of string constraints"""

from collections import defaultdict
from itertools import ifilter

def satisfiable(pos_cons, neg_cons):
    """A function for analysing constraints of the form e.g.

        [a="v1"][a|="v2"]:not([a~="v3"]):not([a$="v4"])"

    :param pos_cons:
        a Set() of pairs (op, v) giving positive constraints on the attribute a,
        where op is a String from "=", "|=", "~=", &c. and v is a String giving the
        RHS.

    :param neg_cons:
        a Set() of pairs (op, v) giving negative constraints (appearing in
        :not()) on the attribute a, where op is a String from "=", "|=", "~=",
        &c. and v is a String giving the RHS.

    :returns:
        True if the constraints are satisfiable are there are an infinite number
        of possible solutions.
        False if there are no solutions.
        A String if there is a unique solution.
    """

    if len(pos_cons) + len(neg_cons) > 1:

        # pos/negmap[op] = set of values v such that [a op v]

        posmap = defaultdict(set)
        for (op, v) in pos_cons:
            posmap[op].add(v)
        negmap = defaultdict(set)
        for (op, v) in neg_cons:
            negmap[op].add(v)

        # Catch basic case of lots of ~= from class constraints
        # Satisfiable as long as we don't have a ~= x and :not(a ~= x)
        if ((len(negmap) == 0 or
             (len(negmap) == 1 and next(iter(negmap)) == "~=")) and
            (len(posmap) == 0 or
             (len(posmap) == 1 and next(iter(posmap)) == "~="))):
            return not any(v in posmap["~="] for v in negmap["~="])

        # Catch igloo case of two equality constraints
        # a = x & a = y   with x != y
        if (len(posmap) == 1 and
            next(iter(posmap)) == "=" and
            len(posmap["="]) > 1):
            return False

        # Catch reveal.css constraints
        # a = x and :not(a = y)
        if (len(posmap) == 1 and
            next(iter(posmap)) == "=" and
            len(negmap) == 1 and
            next(iter(negmap)) == "="):
            return not any(v in posmap["="] for v in negmap["="])

        # Catch reveal.css constraints
        # a exists (by any operator) and :not(a)
        if (len(posmap) > 0 and
            len(negmap) == 1 and
            next(iter(negmap)) == "exists"):
            return False

        # Catch a test case constraint
        # a *= b and :not(a = d)
        if (len(posmap) == 1 and
            next(iter(posmap)) == "*=" and
            len(posmap["*="]) == 1 and
            len(negmap) == 1 and
            next(iter(negmap)) == "=" and
            len(negmap["="]) == 1):
            return True

        # Catch only positive substring guards (*= or ~=) and at most one ^= and $=
        if (len(negmap) == 0 and
            len(posmap["^="]) <= 1 and
            len(posmap["$="]) <= 1 and
            len(posmap["|="]) == 0 and
            len(posmap["="]) == 0):
            return True


        print "WARNING: String Constraints Unknown, assuming True!"
        print "Pos cons: ", pos_cons
        print "Neg cons: ", neg_cons

    return True # TODO

