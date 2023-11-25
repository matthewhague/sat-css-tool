
"""Functions for analysing the satisfiability of string constraints"""

from collections import defaultdict
from itertools import combinations

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

    # if pos_cons contains more than one element, remove "exists"
    # since the attribute having a value implies it exists
    if len(pos_cons) > 1:
        pos_cons.discard(("exists", None))

    if len(pos_cons) + len(neg_cons) > 1:

        # pos/negmap[op] = set of values v such that [a op v]

        posmap = dict()
        for (op, v) in pos_cons:
            if op not in posmap:
                posmap[op] = set()
            posmap[op].add(v)
        negmap = dict()
        for (op, v) in neg_cons:
            if op not in negmap:
                negmap[op] = set()
            negmap[op].add(v)

        def getpos(op):
            if op in posmap:
                return posmap[op]
            return set()

        def getneg(op):
            if op in negmap:
                return negmap[op]
            return set()

        # Catch basic case of lots of ~= from class constraints
        # Satisfiable as long as we don't have a ~= x and :not(a ~= x)
        if ((len(negmap) == 0 or
             (len(negmap) == 1 and next(iter(negmap)) == "~=")) and
            (len(posmap) == 0 or
             (len(posmap) == 1 and next(iter(posmap)) == "~="))):
            return not any(v in getpos("~=") for v in getneg("~="))

        # Catch igloo case of two equality constraints
        # a = x & a = y   with x != y
        if (len(posmap) == 1 and
            next(iter(posmap)) == "=" and
            len(getpos("=")) > 1):
            return False

        # Catch reveal.css constraints
        # a = x and :not(a = y)
        if (len(posmap) == 1 and
            next(iter(posmap)) == "=" and
            len(negmap) == 1 and
            next(iter(negmap)) == "="):
            return not any(v in getpos("=") for v in getneg("="))

        # Catch reveal.css constraints
        # a exists (by any operator) and :not(a)
        if (len(posmap) > 0 and "exists" in negmap):
            return False

        # Catch a test case constraint
        # a *= b and :not(a = d)
        if (len(posmap) == 1 and
            next(iter(posmap)) == "*=" and
            len(getpos("*=")) == 1 and
            len(negmap) == 1 and
            next(iter(negmap)) == "=" and
            len(getneg("=")) == 1):
            return True

        # Catch only positive substring guards (*= or ~=) and at most one ^= and $=
        if (len(negmap) == 0 and
            len(getpos("^=")) <= 1 and
            len(getpos("$=")) <= 1 and
            len(getpos("|=")) == 0 and
            len(getpos("=")) == 0):
            return True

        # Only positive equals (can't take two diff vals)
        if (len(negmap) == 0 and
            len(posmap) == 1 and "=" in posmap):
            return len(getpos("=")) <= 1

        # Only negative equals
        if (len(posmap) == 0 and
            len(negmap) == 1 and "=" in negmap):
            return True

        # Catch only equality constraints in neg and pos, and no overlap
        if (len(posmap) == 1 and "=" in posmap and
            len(negmap) == 1 and "=" in negmap):
            return (len(getpos("=")) <= 1 and
                    getpos("=").isdisjoint(getneg("=")))

        # Conflicting lang requirements
        if (len(posmap) == 1 and "|=" in posmap and
            len(negmap) == 0):
            for l1, l2 in combinations(getpos("|="), 2):
                if not (str.startswith(l1, l2 + "-") or
                        str.startswith(l2, l1 + "-")):
                    return False
            return True

        print("WARNING: String Constraints Unknown, assuming True!")
        print("Pos cons: ", pos_cons)
        print("Neg cons: ", neg_cons)
        print("Pos map len", len(posmap))
        print("has |=", "|=" in posmap)
        print("Pos map", posmap)

    return True # TODO

