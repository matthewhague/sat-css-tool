
"""Functions for checking emptiness of a CSS automaton"""

import copy
from collections import defaultdict
from itertools import chain, product
from timeit import default_timer

from z3 import *

import cssfile
import cssautomaton
from cssautomaton import CSSAutomaton, Tran, Arrow
import stringcons

# define specified id and class attribute names and namespaces
# None is really default, but assuming we're just going to get CSS for HTML
# where namespaces aren't really used...
specialns = ""
classatt = "class"
idatt = "id"
langatt = "lang"

_locally_checkable_ps = set(["link", "visited", "hover",
                             "active", "focus", "enabled",
                             "disabled", "checked",
                             "valid", "invalid"])
_local_conflict_ps = frozenset([("link", "visited"),
                                ("enabled", "disabled"),
                                ("valid", "invalid")])

_global_ps = ["target", "root", "empty"]

_of_type_cons = set(["nth-of-type",
                     "nth-last-of-type",
                     "first-of-type",
                     "only-of-type",
                     "last-of-type"])

_known_ps = (_locally_checkable_ps |
             _local_conflict_ps |
             set(_global_ps) |
             _of_type_cons |
             set(["first-child", "last-child", "only-child"]))

_emp_z3 = Solver()

_enum_count = 0
def _get_next_enum_id():
    """Bit of a hack so we can create EnumSort for each automaton"""
    global _enum_count
    new_id = _enum_count
    _enum_count += 1
    return str(new_id)

class HashableZ3:
    """Some kind of hashable constraints for z3 constraints and variables"""
    def __init__(self, z3):
        self.z3 = z3

    def __eq__(self, other):
        return self is other

    def __hash__(self):
        return id(self)

    def __str__(self):
        return str(self.z3)

    def __repr__(self):
        return str(self.z3) + "<" + str(id(self)) + ">"

class AutEmptinessException(Exception):
    pass

def get_local_conflict_ps():
    """
    :returns:
        Set of pairs of pseudo classes (p1, p2) that cannot occur on same node
        (note, if we have (p1, p2) we don't have (p2, p1)
    """
    return _local_conflict_ps

def isempty(aut, data=None):
    """Checks using SAT whether the given CSSAutomaton is empty

    :param aut"
        The automaton to check for emptiness as a CSSAutomaton
    :param data:
        Some debug data to print for slow checks
    :returns:
        True iff the automaton is empty
    """
    from main import get_unopt_emp
    if get_unopt_emp():
        return isempty_unoptimised(aut, data)
    else:
        return isempty_optimised(aut, data)

def isempty_optimised(aut, data=None):
    """Checks using SAT whether the given CSSAutomaton is empty

    :param aut"
        The automaton to check for emptiness as a CSSAutomaton
    :param data:
        Some debug data to print for slow checks
    :returns:
        True iff the automaton is empty
    """
    naut = _normalise_automaton(aut)
    checker = AutEmptinessChecker(naut)
    return checker.check()

def _normalise_automaton(aut):
    """Builds a new normalised automaton without class, local pseudo,
    or attr constraints, and only #id constraints if needed.

    :param aut:
        The automaton to normalise as a CSSAutomaton
    :returns:
        A new CSSAutomaton with normalised transitions
    """
    naut = CSSAutomaton()
    naut.qinit = aut.qinit
    naut.qfinal = aut.qfinal
    for t in aut:
        sel = _normalise_selector(t.node_selector)
        if sel is not None:
            naut.add_tran(Tran(t.q1,
                               t.arrow,
                               sel,
                               t.q2))
    return naut

def _normalise_selector(sel):
    """Normalises the selector, which means (at all steps,
       return None if selector becomes unsatisfiable):

            + Replaces .c with [class~="c"] (even in :not)
            + Removes attribute tests on ID elements:
                + translate #i to [id="i"] (even in :not)
                + if attribute tests on id imply a fixed value v for id
                  then add #v
                + remove all attribute tests on id if they are satisfiable
                + else return None
            + Removes attribute selectors if they're satisfiable.
                + else return None
    :param sel:
        The selector as Selector.parsed_tree from cssselect
    :returns:
        The normalised selector, or None if its inconsistent
    """
    nocls = _normalise_classes(sel)
    if nocls is None:
        return None
    noids = _normalise_ids(nocls)
    if noids is None:
        return None
    normlang = noids
    normlang = _normalise_lang(noids)
    if normlang is None:
        return None
    noatts = _normalise_atts(normlang)
    if noatts is None:
        return None
    return _normalise_pseudo_selectors(noatts)

def _selector_get_constraints(sel, do_simple_sel):
    """Removes special constraints from a selector and returns sets of them.

    :param sel:
        The selector as Selector.parsed_tree from cssselect
    :param do_simple_sel:
        A function do_simple_sel(s, n) that takes a simple selector s (with no negation)
        and a boolean n that indicates if s appears inside a negation,
        and returns None if the selector is not one to be removed and a
        constraint c of some type T
    :returns:
        (newsel, pos_cons, neg_cons)
        Where s is the selector without the constraints that weren't None for
        do_simple_set
        pos_cons is the set of constraints returned by do_simple_set for positive cons
        net_cons is the set of constraints returned by do_simple_sel for negative cons
    """
    stype = type(sel).__name__

    (newsel, pos_cons, neg_cons) = (
        _selector_get_constraints(sel.selector, do_simple_sel)
            if stype != "Element"
            else (sel, set([]), set([]))
    )

    cons = None
    if stype == "Negation":
        cons = do_simple_sel(sel.subselector, True)
        if cons is not None:
            neg_cons.add(cons)
    else:
        cons = do_simple_sel(sel, False)
        if cons is not None:
            pos_cons.add(cons)

    if cons is not None:
        return (newsel, pos_cons, neg_cons)
    else:
        cpy = copy.copy(sel)
        cpy.selector = newsel
        return (cpy, pos_cons, neg_cons)

def _normalise_special(sel, do_simple_sel):
    """Removes special simple constraints on a special attribute (e.g. .c for class and
    #i for id) from the selector as per _normalise_selector.

    :param sel:
        The selector as Selector.parsed_tree from cssselect
    :param do_simple_sel:
        A function do_simple_sel(s, n) that takes a simple selector s (with no negation)
        and a boolean n that indicates if s appears inside a negation,
        and returns None if the selector is not one to be normalised and (op, v) if
        it imposes the constraint [a op v] on the special attribute a.  op is a string
        from "=", "|=", "~=", &c. and v is a string value.
    :returns:
        (s, v) or None
        Where s is the normalised selector -- i.e. all special constraints removed.
        And v is a string that is not None if the (op, s) constraints imply a fixed value
        of the attribute (e.g. [a ~= "one"]:not([a *= " "]) implies a = "one".
        None is returned if the constraints are not satisfiable
    """
    (newsel, pos_cons, neg_cons) = _selector_get_constraints(sel, do_simple_sel)

    sat = stringcons.satisfiable(pos_cons, neg_cons)
    if sat is True:
        return (newsel, None)
    elif sat is False:
        return None
    else:
        return (newsel, sat)

def _normalise_classes(sel):
    """Normalises the class constraints, removing them if they are satisfiable,
    returning None if they are not.

    :param sel:
        The selector to normalise
    :returns:
        The selector with the class constraints removed if they are satisfiable,
        None if they are not
    """
    def do_simple_sel(s, neg):
        stype = type(s).__name__
        if stype == "Class":
            return ("~=", s.class_name)
        elif stype == "Attrib":
            if ((s.namespace == specialns or (s.namespace is None and neg)) and
                 s.attrib == classatt):
                return (s.operator, s.value)
        return None
    norm = _normalise_special(sel, do_simple_sel)
    return norm[0] if norm is not None else None

def _normalise_ids(sel):
    """Normalises the ID constraints from the selector as per _normalise_selector.

    :param sel:
        The selector as Selector.parsed_tree from cssselect
    :returns:
        The normalised selector, or None if its inconsistent wrt IDs
    """
    def do_simple_sel(s, neg):
        stype = type(s).__name__
        if stype == "Hash":
            return ("=", s.id)
        elif stype == "Attrib":
            if ((s.namespace == specialns or (s.namespace is None and neg)) and
                 s.attrib == idatt):
                return (s.operator, s.value)
        return None

    norm = _normalise_special(sel, do_simple_sel)

    if norm is None:
        return None
    else:
        (s, v) = norm
        return s if v is None else Hash(s, v)

def _normalise_lang(sel):
    """Normalises the lang constraints from the selector.  Similar to
    _normalise_classes.

    :param sel:
        The selector as Selector.parsed_tree from cssselect
    :returns:
        The normalised selector, or None if its inconsistent.
    """
    def do_simple_sel(s, neg):
        stype = type(s).__name__
        if stype == "Function" and s.name == "lang":
            if len(s.arguments) < 1:
                raise AutEmptinessException("Invalid lang function has no arguments")
            return ("|=", s.arguments[0].value)
        elif stype == "Attrib":
            if ((s.namespace == specialns or (s.namespace is None and neg)) and
                 s.attrib == langatt):
                return (s.operator, s.value)
        return None
    norm = _normalise_special(sel, do_simple_sel)
    return norm[0] if norm is not None else None

def _normalise_atts(sel):
    """Removes the attribute constraints from the selector as per _normalise_selector.

    :param sel:
        The selector as Selector.parsed_tree from cssselect
    :returns:
        The normalised selector, or None if its inconsistent wrt attributes
    """
    # Strategy: build up a dictionary
    #
    #     (ns, a) => (pos_cons, neg_cons)
    #
    # which are constraints (op, v)
    #
    # For (None, a) then neg_cons need to be conjuncted to all neg_cons for
    # (ns, a) and pos_cons can be treated as if they all have their own unique
    # namespace (still subject to (None, a) neg constraints).

    def do_selector(s):
        """:returns: (newsel, dictionary)"""

        stype = type(s).__name__

        (newsel, cons) = (
            do_selector(s.selector)
                if stype != "Element"
                else (s, defaultdict(lambda : (set([]), set([]))))
        )

        att_sel = s
        idx = 0
        if stype == "Negation":
            att_sel = s.subselector
            idx = 1

        if type(att_sel).__name__ == "Attrib":
            cons[(att_sel.namespace,
                  att_sel.attrib)][idx].add((att_sel.operator,
                                             att_sel.value))
            return (newsel, cons)
        else:
            cpy = copy.copy(s)
            cpy.selector = newsel
            return (cpy, cons)

    (newsel, cons) = do_selector(sel)

    # check all satisfiable
    # if not return None
    for (ns, a), (pos_cons, neg_cons) in cons.items():
        gen_negs = cons[(None, a)][1] if (None, a) in cons else set([])
        all_negs = neg_cons.union(gen_negs)
        if not stringcons.satisfiable(pos_cons, all_negs):
            return None

    return newsel

def _normalise_pseudo_selectors(sel):
    """Normalises the pseudo selector constraints, removing the ones that can be
    checked locally.  Returns None if they are not.

    :param sel:
        The selector to normalise
    :returns:
        The selector with the locally checkable pseudo selector constraints removed
        if they are satisfiable, None if they are not
    """
    def do_simple_sel(s, neg):
        stype = type(s).__name__
        if stype == "Pseudo" and s.ident in _locally_checkable_ps:
            return s.ident
        if stype == "Pseudo" and s.ident not in _known_ps:
            print("WARNING: unrecognised pseudo class '", s.ident, "' in '", cssfile.selector_str_pt(sel), "' treating as simple boolean")
            return s.ident
        return None

    (newsel, pos_cons, neg_cons) = _selector_get_constraints(sel, do_simple_sel)

    # check no direct contradiction
    if not pos_cons.isdisjoint(neg_cons):
        return None

    # check no two conflicting forced to be true
    for (ps1, ps2) in _local_conflict_ps:
        if ps1 in pos_cons and ps2 in pos_cons:
            return None

    return newsel


class PositionVariables:
    """Container class for position variables used by AutEmptinessChcker

    Fields (may be None, initially None):
        pv = Z3 Int variable, position of current node
        nlast = Z3 Int variable, position of last node in sibling arrangement
        tsumpv = dict where tsumpv[(ns,e)] for namespace and element is number
                 of strictly preceding nodes for that type up to position pv
        tsum = dict where tsum[(ns,e)] for namespace and element is total number
               of given type in row
        ns = Z3 variable for namespace
        ele = Z3 variable for element
    """

    pv = None
    nlast = None
    tsumpv = None
    tsum = None
    ns = None
    ele = None

    def __eq__(self, other):
        return self is other

    def __hash__(self):
        return id(self)


class AutEmptinessChecker:
    """Emptiness checker for normalised a given CSSAutomaton"""

    __nvar = Int("n")
    __bvar = Int("b")
    __nlast = Int("nlast")
    __delta = Int("d")
    __next_pos_var = 0
    __next_ns_var = 0
    __next_ele_var = 0
    __next_sumpv_var = 0

    def __init__(self, aut):
        """Constructs an emptiness checker for aut.  Call check() to check.

        :param aut:
            A normalised (with _normalise_automaton) CSSAutomaton
        """
        # TODO: make use of __ and not consistent...

        self.aut = aut
        self.last = self.__has_last_constraints()
        self.of_type = self.__has_of_type_constraints()
        # Note, we must have last_of_type => of_type
        self.last_of_type = self.__has_last_of_type_constraints()

        # get set of namespaces and elements that we might need
        comps = self.aut.components()
        self.nss = list(comps.namespaces)
        self.eles = list(comps.elements)
        # add dummies for all transitions that might need them
        self.nss.append("_null_ns")
        self.eles.append("_null_ele")
        i = 0
        for t in self.aut:
            (dummy_ns, dummy_ele) = self.__get_tran_dummies(t)
            if dummy_ns:
                self.nss.append("_dummy_ns" + str(i))
                i += 1
            if dummy_ele:
                self.eles.append("_dummy_ele" + str(i))
                i += 1

        self._enum_id = _get_next_enum_id()

        self.nssort, vals = EnumSort(
            "Namespace" + self._enum_id, list(map(str, self.nss))
        )
        self.nsvals = { ns : v for (ns, v) in zip(self.nss, vals) }

        self.esort, vals = EnumSort(
            "Element" + self._enum_id, list(map(str, self.eles))
        )
        self.evals = { e : v for (e, v) in zip(self.eles, vals) }

        self.__tdelta = { (ns, e) : Int("d" + str((ns, e)))
                          for (ns, e) in product(self.nss, self.eles) }
        self.__tsum = { (ns,e) : Int("sum" + str((ns, e)))
                        for (ns, e) in product(self.nss, self.eles) }


    def __has_pseudo_elements(self, cons):
        """
        :param cons:
            A set of pseudo element / function names as strings
        :returns:
            True iff something from cons appears in a transition of self.aut
        """
        for t in self.aut:
            if self.__sel_has_pseudo_elements(t.node_selector, cons):
                return True
        return False

    def __sel_has_pseudo_elements(self, sel, cons, neg_cons = None):
        """Returns true if selector has any of the of type constraints in cons

        :param sel:
            The selector in cssselect parsed_tree format
        :param cons:
            A python set of strings, the strings being the names of pseudo
            elements such as "last-of-type"
        :param neg_cons:
            If specified, then cons will only refer to positive selectors
            and neg_cons will be selectors in :not()
        :returns:
            True iff there is an selector from cons in sel
        """
        if neg_cons is None:
            neg_cons = cons

        s = sel
        while type(s).__name__ != "Element":
            check_sel = s
            check_cons = cons
            if type(s).__name__ == "Negation":
                check_sel = s.subselector
                check_cons = neg_cons
            t = type(check_sel).__name__
            if (t == "Pseudo" and check_sel.ident in check_cons):
                return True
            if (t == "Function" and check_sel.name in check_cons):
                return True
            s = s.selector
        return False



    def __has_last_constraints(self):
        cons = set(["nth-last-child",
                    "nth-last-of-type",
                    "last-child",
                    "only-child",
                    "last-of-type",
                    "only-of-type"])
        return self.__has_pseudo_elements(cons)

    def __has_of_type_constraints(self):
        """Looks through aut to see if it has any "of type" constraints

        :returns:
            True iff self.aut contains some of type constraints
        """
        return self.__has_pseudo_elements(_of_type_cons)


    def __has_last_of_type_constraints(self):
        """Looks through aut to see if it has any "last of type" constraints

        :returns:
            True iff self.aut contains some of type constraints
        """
        cons = set(["nth-last-of-type",
                    "only-of-type",
                    "last-of-type"])
        return self.__has_pseudo_elements(cons)


    def __get_tran_dummies(self, t):
        """
        :param t:
            A transition Tran
        :returns:
            (dummy_ns, dummy_ele)
            where dummy_ns is True iff transition implies need for a dummy namespace
            and dummy_ele is True iff transition implies need for a dummy element
        """

        sel = t.node_selector

        # if selector is just * no dummy required
        if (type(sel).__name__ == "Element" and
            sel.namespace is None and
            sel.element is None):
            return (False, False)

        # else find if it forces namespace or element, and if it has an of-type
        # requirement
        is_of_type = self.__sel_has_pseudo_elements(sel, _of_type_cons)

        if not is_of_type:
            return (False, False)

        while type(sel).__name__ != "Element":
            sel = sel.selector

        if sel.namespace == None:
            return (True, False)
        elif sel.element == None:
            return (False, True)
        else:
            return (False, False)


    def check(self):
        """A SAT free emptiness check for automata that don't have any counting
        Note, this method implicity uses the fact
        that noop transitions only occur on the way to the final state.

        TODO: is that true about noops?

        :returns:
            True iff aut (passed to __init__) is empty
        """

        # Then do (loop-free) backwards reachability check, worklist of tuples
        #
        #    (q,
        #     ids, target, root,
        #     arrs,
        #     pos_cons, pvs, pd, p*)
        #
        # which means you can accept from q, using the set of IDs in ids and target
        # is true iff one of the nodes had to have :target.  Root means the state
        # has to be applied at the root of the tree (i.e. only noop transitions can
        # be applied).
        #
        # arrs is the set of arrows that have been applied without changing the
        # state (to avoid using loops infinitely with the same op)
        #
        # pos_cons is a set of constraints in HashableZ3 format on current set
        # of siblings  That is, a set of HashableZ3 formulas giving constraints
        # on the positions.  Generally of the form
        #
        #   (E)n pi = an + b (for nth-child)
        #   (E)n N - pi = an + b (nth-last-child)
        #   (E)n pi = p(i+1) - a - n (a is constant, for relationships between neighbours)
        #
        # pv is PositionVariables for the last node that needed them or None
        # pd is the constant distance from pv (or the end if pv is None) (never
        #    more than 1 when of-type needed)
        # p* is True if pd is a lower bound not exact (i.e. there was a ~ on the
        # way)

        worklist = set([(self.aut.qfinal,
                         frozenset(), False, False,
                         frozenset(),
                         frozenset(), None, 0, False)])
        donelist = set()

        # don't need a done list because we only have self-loops and the arrs field
        # prevents looping on a single state

        while len(worklist) > 0:
            oldtup = worklist.pop()
            (q,
             ids, targ, root,
             arrs,
             pos_cons, pvs, pd, pdstar) = oldtup
            donelist.add(oldtup)

            for t in self.aut.trans[q]:
                if root and not t.arrow == Arrow.noop:
                    continue
                if t.q1 == t.q2 and t.q1 == q and t.arrow in arrs:
                    continue

                new_pvs = pvs if t.arrow == Arrow.noop else None

                (sat,
                 tids, ttarg, troot, tempty,
                 tpos_cons, new_pvs) = self.__get_sel_info(t.node_selector)

                if (sat and
                    tids.isdisjoint(ids) and
                    not (targ and ttarg) and
                    # here we use that noop transition only go to final state and
                    # say if we have to be empty, we can't go immediately down
                    not (tempty and t.arrow == Arrow.child) and
                    not (troot and t.arrow in [Arrow.neighbour, Arrow.sibling]) and
                    # if going up the tree, make sure we can satisfy the nth-child
                    # constraints
                    (t.arrow != Arrow.child or
                     self.__pos_cons_satisfiable(pos_cons,
                                                 pvs,
                                                 pd,
                                                 pdstar,
                                                 1))):

                    new_arrs = set([t.arrow])
                    if t.q1 == q:
                        new_arrs |= arrs

                    new_pos_cons = set(tpos_cons)
                    new_pd = 0
                    new_pdstar = False
                    if t.arrow == Arrow.noop:
                        new_pos_cons |= pos_cons
                        if new_pvs is not None:
                            new_pos_cons.add(self.__get_pos_constraint(new_pvs,
                                                                       pvs,
                                                                       pd,
                                                                       pdstar))
                        else:
                            new_pd = pd
                            new_pdstar = pdstar
                            new_pvs = pvs
                    elif t.arrow == Arrow.neighbour:
                        new_pos_cons |= pos_cons
                        if new_pvs is not None:
                            new_pos_cons.add(self.__get_pos_constraint(new_pvs,
                                                                       pvs,
                                                                       pd + 1,
                                                                       pdstar))
                        else:
                            new_pd = pd + 1
                            new_pdstar = pdstar
                            new_pvs = pvs
                    elif t.arrow == Arrow.sibling:
                        new_pos_cons |= pos_cons
                        if new_pvs is not None:
                            new_pos_cons.add(self.__get_pos_constraint(new_pvs,
                                                                       pvs,
                                                                       pd + 1,
                                                                       True))
                        else:
                            new_pd = pd + 1
                            new_pdstar = True
                            new_pvs = pvs

                    if (t.q1 == self.aut.qinit and
                        # root can't have position constraints cos it's not a
                        # child
                        (not troot or len(new_pos_cons) == 0) and
                        self.__pos_cons_satisfiable(new_pos_cons,
                                                    new_pvs,
                                                    new_pd,
                                                    new_pdstar)):
                        return False

                    newtup = (t.q1,
                              frozenset(ids.union(tids)), targ or ttarg, troot,
                              frozenset(new_arrs),
                              frozenset(new_pos_cons), new_pvs, new_pd, new_pdstar)

                    if newtup not in donelist:
                        worklist.add(newtup)

        # we abort early if we find q0 (which would show non-emp)
        return True

    def __new_sumpv_var(self, ns, e):
        """
        :param ns:
            namespace
        :param e:
            element
        :returns:
            A fresh Z3 integer variable psum(ns,e)i
        """
        v = Int("psum" + str((ns, e)) + str(self.__next_sumpv_var))
        self.__next_sumpv_var += 1
        return v

    def __new_pos_var(self):
        """
        :returns:
            A fresh Z3 integer variable pi
        """
        v = Int("p" + str(self.__next_pos_var))
        self.__next_pos_var += 1
        return v

    def __new_ns_var(self):
        """
        :returns:
            A fresh Z3 namespace variable pi
        """
        v = Const("ns" + str(self.__next_ns_var),
                  self.nssort)
        self.__next_ns_var += 1
        return v

    def __new_ele_var(self):
        """
        :returns:
            A fresh Z3 integer variable pi
        """
        v = Const("ele" + str(self.__next_ele_var),
                  self.esort)
        self.__next_ele_var += 1
        return v

    def __pos_cons_satisfiable(self, pos_cons, pvs, pd, pdstar, fixed_pos = None):
        """
        :param pos_cons:
            A set of HashableZ3 equations (x + d + 1) &c.
        :param pvs:
            The PositionVariables of the next node that has one (Z3 Int var)
        :param pd:
            The fixed part of the distance to the next pv (Integer)
        :param pdstar:
            Whether pd can be arbitrarily increased (Boolean)
        :param fixed_pos:
            An integer n if the current node has to be the nth child.  If None, then a
            variable position is allowed.
        :returns:
            True iff pos_cons can be satisfied
        """
        global _emp_z3

        if len(pos_cons) == 0:
            return True

        _emp_z3.push()

        (pos_pvs, new_cons) = self.__create_new_pvs(fixed_pos)

        for c in chain(pos_cons,
                       new_cons):
            _emp_z3.add(c.z3)

        c = self.__get_pos_constraint(pos_pvs, pvs, pd, pdstar)
        _emp_z3.add(c.z3)

        res = _emp_z3.check()

        _emp_z3.pop()

        return res == sat


    def __get_pos_constraint(self, pvs, next_pvs, pd, pdstar):
        """
        :param pvs:
            The PositionVariables of the current node
        :param next_pvs:
            The PositionVariables of the next node with position vars
            or None if there is none
        :param pd:
            Minimum distance between pvs and next_pvs
        :param pdstar:
            True iff the distance can be arbitrarily pumped
        :returns:
            A HashableZ3 constraint enforcing pvs is right distance from
            next_pvs
        """

        if next_pvs is None:
            # always satisfiable!
            return HashableZ3(And())

        cons = []
        evars = []

        of_type = self.of_type or self.last_of_type

        if of_type:
            for (ns, e) in product(self.nss, self.eles):
                d = self.__tdelta[(ns,e)]
                evars.append(d)
                cons.append(d >= 0)
                cons.append(Implies(And(pvs.ns == self.nsvals[ns],
                                        pvs.ele == self.evals[e],
                                        pvs.pv < next_pvs.pv),
                                    d >= 1))
                cons.append(next_pvs.tsumpv[(ns,e)]
                            ==
                            pvs.tsumpv[(ns,e)] + d)

        if pdstar:
            evars.append(self.__delta)
            cons.append(next_pvs.pv == pvs.pv + pd + self.__delta)
            cons.append(self.__delta >= 0)
            if of_type:
                cons.append(self.__delta + pd == Sum(list(self.__tdelta.values())))
        else:
            cons.append(next_pvs.pv == pvs.pv + pd)
            if of_type:
                cons.append(pd == Sum(list(self.__tdelta.values())))

        if len(evars) > 0:
            return HashableZ3(Exists(evars, And(cons)))
        else:
            return HashableZ3(And(cons))


    def __get_sel_info(self, sel):
        """
        :param sel:
            A cssselect parsed_tree selector normalised and with no numeric
            constraints such as nth-child.
        :param pv:
            Variable giving the position of the node if already determined, else
            None (HashableZ3)
        :returns:
            (sat, ids, targ, root, empty, pos_cons, node_pos)
            sat is True iff the local part of the selector can be satisfied
            ids is the set of ids that the node must have
            targ is True iff the node must be the page target
            root is True iff the node must be the root
            empty is True iff the node must have no children
            pos_cons is a set of HashableZ3 constraints on the position of the node
            pvs is the PositionVariables in the constraints or None if not used.
        """

        # TODO: fix this so that we don't have if pv is None all over

        # Strategy: go through selector and collect negative constraints on element,
        # namespace, target, and root.  (There will be no negative IDs due to
        # normalisation)

        # set of pairs (ns, ele) with None for *
        neg_nsele = set()
        ps = set()
        neg_ps = set()
        ids = set()
        pos_cons = set()
        pvs = None

        s = sel
        while type(s).__name__ != "Element":
            stype= type(s).__name__
            if stype == "Negation":
                subtype = type(s.subselector).__name__
                if subtype == "Element":
                    neg_nsele.add((s.subselector.namespace,
                                   s.subselector.element))
                elif subtype == "Pseudo":
                    if s.subselector.ident == "first-child":
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(pvs.pv > 1))
                    elif s.subselector.ident == "last-child":
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(pvs.nlast - pvs.pv > 0))
                    elif s.subselector.ident == "only-child":
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(Or(pvs.pv > 1,
                                                   pvs.nlast - pvs.pv == 0)))
                    elif s.subselector.ident == "first-of-type":
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(self.__not_nth_of_type(pvs, 0, 1)))
                    elif s.subselector.ident == "only-of-type":
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(Or(HashableZ3(self.__not_nth_of_type(pvs, 0, 1)),
                                        HashableZ3(self.__nth_last_of_type(pvs, 0, 1))))
                    elif s.subselector.ident == "last-of-type":
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(self.__not_nth_last_of_type(pvs, 0, 1)))
                    else:
                        neg_ps.add(s.subselector.ident)
                elif subtype == "Function":
                    if s.subselector.name == "nth-child":
                        a, b = cssfile.get_fun_sel_coefs(s.subselector)
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(self.__not_nth(pvs.pv, a, b)))
                    elif s.subselector.name == "nth-last-child":
                        a, b = cssfile.get_fun_sel_coefs(s.subselector)
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(self.__not_nth(pvs.nlast - pvs.pv + 1, a, b)))
                    elif s.subselector.name == "nth-of-type":
                        a, b = cssfile.get_fun_sel_coefs(s.subselector)
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(self.__not_nth_of_type(pvs, a, b)))
                    elif s.subselector.name == "nth-last-of-type":
                        a, b = cssfile.get_fun_sel_coefs(s.subselector)
                        if pvs is None:
                            (pvs, new_cons) = self.__create_new_pvs()
                            pos_cons |= new_cons
                        pos_cons.add(HashableZ3(self.__not_nth_last_of_type(pvs, a, b)))
                    else:
                        raise AutEmptinessException("Unrecognised function selector " +
                                                    str(sel))
            elif stype == "Pseudo":
                if s.ident == "first-child":
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(pvs.pv == 1))
                elif s.ident == "last-child":
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(pvs.nlast - pvs.pv == 0))
                elif s.ident == "only-child":
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(pvs.pv == 1))
                    pos_cons.add(HashableZ3(pvs.nlast - pvs.pv == 0))
                elif s.ident == "first-of-type":
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(self.__nth_of_type(pvs, 0, 1)))
                elif s.ident == "only-of-type":
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(self.__nth_of_type(pvs, 0, 1)))
                    pos_cons.add(HashableZ3(self.__nth_last_of_type(pvs, 0, 1)))
                elif s.ident == "last-of-type":
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(self.__nth_last_of_type(pvs, 0, 1)))
                else:
                    ps.add(s.ident)
            elif stype == "Hash":
                ids.add(s.id)
            elif stype == "Function":
                if s.name == "nth-child":
                    a, b = cssfile.get_fun_sel_coefs(s)
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(self.__nth(pvs.pv, a, b)))
                elif s.name == "nth-last-child":
                    a, b = cssfile.get_fun_sel_coefs(s)
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(self.__nth(pvs.nlast - pvs.pv + 1, a, b)))
                elif s.name == "nth-of-type":
                    a, b = cssfile.get_fun_sel_coefs(s)
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(self.__nth_of_type(pvs, a, b)))
                elif s.name == "nth-last-of-type":
                    a, b = cssfile.get_fun_sel_coefs(s)
                    if pvs is None:
                        (pvs, new_cons) = self.__create_new_pvs()
                        pos_cons |= new_cons
                    pos_cons.add(HashableZ3(self.__nth_last_of_type(pvs, a, b)))
                else:
                    raise AutEmptinessException("Unrecognised function selector " +
                                                str(sel))
            s = s.selector

        sat = (not ((s.namespace, s.element) in neg_nsele or
                   (None, s.element) in neg_nsele) and
               ps.isdisjoint(neg_ps))

        if (self.of_type or self.last_of_type) and pvs is not None:
            if s.element is not None:
                pos_cons.add(HashableZ3(pvs.ele == self.evals[s.element]))
            if s.namespace is not None:
                pos_cons.add(HashableZ3(pvs.ns == self.nsvals[s.namespace]))

            for (ns, e) in neg_nsele:
                if ns is not None and e is not None:
                    pos_cons.add(HashableZ3(Or(pvs.ns != self.nsvals[ns],
                                                pvs.ele != self.evals[e])))
                elif ns is None and e is not None:
                    pos_cons.add(HashableZ3(pvs.ele != self.evals[e]))
                elif ns is not None and e is None:
                    pos_cons.add(HashableZ3(pvs.ns != self.nsvals[ns]))
                elif ns is None and e is None:
                    # not(*|*) is False
                    pos_cons.add(HashableZ3(Or()))

        return (sat,
                ids, "target" in ps, "root" in ps, "empty" in ps,
                pos_cons, pvs)


    def __create_new_pvs(self, fixed_pos = None):
        """
        :param fixed_pos:
            If None then a free variable is created for the position
            Else, pass an integer and this will be the value of pvs.pv

        :returns:
            (pvs, new_cons)
            where
                pvs is a PositionVariables
                new_cons is a list of HashableZ3 constraints over the new variables
        """
        pvs = PositionVariables()
        cons = set()

        pvs.pv = self.__new_pos_var() if fixed_pos is None else fixed_pos
        cons.add(HashableZ3(pvs.pv >= 1))

        if self.last:
            pvs.nlast = self.__nlast
            cons.add(HashableZ3(pvs.nlast - pvs.pv >= 0))

        if self.of_type or self.last_of_type:
            pvs.tsumpv = { (ns,e) : self.__new_sumpv_var(ns, e)
                           for (ns, e) in product(self.nss, self.eles) }
            cons |= { HashableZ3(pvs.tsumpv[(ns,e)] >=  0)
                      for (ns, e) in product(self.nss, self.eles) }
            cons.add(HashableZ3(pvs.pv == Sum(list(pvs.tsumpv.values()))))
            pvs.ns = self.__new_ns_var()
            pvs.ele = self.__new_ele_var()

        if self.last_of_type:
            pvs.tsum = self.__tsum
            # TODO: this seems fishy -- if sum > 0 then sum - tsumpv > 0 since
            # strict predecessor...
            cons |= { HashableZ3(
                        And(Implies(pvs.tsum[(ns,e)] == 0,
                                    pvs.tsumpv[(ns,e)] == 0),
                            Implies(pvs.tsum[(ns,e)] > 0,
                                    pvs.tsum[(ns,e)] > pvs.tsumpv[(ns,e)]))
                      )
                      for (ns, e) in product(self.nss, self.eles) }
            cons.add(HashableZ3(pvs.nlast == Sum(list(pvs.tsum.values()))))

        return (pvs, cons)

    def __nth(self, x, a, b):
        """Returns an existential Presburger clause enforcing

            (E)n . x = an + b

        :param x:
            z3 Int variable
        :param a:
            constant python integer
        :param b:
            constant python integer
        :returns:
            z3 clause enforcing the above
        """
        if a != 0:
            return Exists([self.__nvar], And(self.__nvar >= 0,
                                             x == a * self.__nvar + b))
        else:
            return x == b

    def __not_nth(self, x, a, b):
        """Returns an existential Presburger clause enforcing

            not (E)n . x = an + b

        :param x:
            z3 Int variable
        :param a:
            constant python integer
        :param b:
            constant python integer
        :returns:
            z3 clause enforcing the above
        """
        if a == 0:
            return x != b

        b1 = b // a
        b2 = b % a
        bnd__b2 = (
            (self.__bvar > -abs(a))
            if (a * b1 < 0)
            else (self.__bvar < abs(a))
        )
        dir__b2 = (
            (self.__bvar <= 0)
            if (a * b1 < 0)
            else (self.__bvar >= 0)
        )
        xvsb = (x < b) if a > 0 else (x > b)
        return Or(xvsb,
                  Exists([self.__nvar, self.__bvar],
                         And(self.__nvar >= 0,
                             bnd__b2,
                             dir__b2,
                             self.__bvar != b2,
                             x == (a*self.__nvar) + (a*b1) + self.__bvar)))


    def __nth_of_type(self, pvs, a, b):
        """Constructs a clause expressing the same as the selector of
        the same name.  an + b for the ith position in the run.

        :param pvs:
            PositionVariables with of type variables
        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :returns:
            Z3 encoding expressing the selector
        """
        return self.__of_type(pvs, a, b, False, self.__nth)

    def __not_nth_of_type(self, pvs, a, b):
        """Constructs a clause expressing the same as the selector of
        the same name, but negated.  Not an + b for the ith position in
        the run.

        :param pvs:
            PositionVariables with of type variables
        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :returns:
            Z3 encoding expressing the selector
        """
        return self.__of_type(pvs, a, b, False, self.__not_nth)

    def __nth_last_of_type(self, pvs, a, b):
        """Constructs a clause expressing the same as the selector of
        the same name.  an + b for the ith position in the run.

        :param pvs:
            PositionVariables with of type variables
        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :returns:
            Z3 encoding expressing the selector
        """
        return self.__of_type(pvs, a, b, True, self.__nth)

    def __not_nth_last_of_type(self, pvs, a, b):
        """Constructs a clause expressing the same as the selector of
        the same name, but negated.  Not an + b for the ith position in
        the run.

        :param pvs:
            PositionVariables with of type variables
        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :returns:
            Z3 encoding expressing the negated selector
        """
        return self.__of_type(pvs, a, b, True, self.__not_nth)


    def __of_type(self, pvs, a, b, is_last, pos_fun):
        """Constructs a clause expressing the node at position i in
        the run is an + bth of type, according to pos_fun

        :param pvs:
            PositionVariables with of type variables
        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :param is_last:
            Boolean saying whether this is a last-of-type check
        :param pos_fun:
            self.__nth or self.__not_nth
        :returns:
            Z3 encoding expressing the selector
        """
        def get_sum(ns, e):
            if is_last:
                return pvs.tsum[(ns,e)] - pvs.tsumpv[(ns,e)]
            else:
                # +1 because first has 0 preceding
                return pvs.tsumpv[(ns,e)] + 1

        return Or([ And(
                         pvs.ns == self.nsvals[ns],
                         pvs.ele == self.evals[e],
                         pos_fun(get_sum(ns, e), a, b)
                    )
                    for (ns, e) in product(self.nss, self.eles) ])


###############################################################################
# Unoptimised version

def isempty_unoptimised(aut, data=None):
    """Checks using SAT whether the given CSSAutomaton is empty

    :param aut"
        The automaton to check for emptiness as a CSSAutomaton
    :param data:
        Some debug data to print for slow checks
    :returns:
        True iff the automaton is empty
    """
    naut = _normalise_automaton(aut)
    _emp_z3.push()

    enc = _Z3NormAutEnc(naut, _emp_z3)
    # Uncomment these if you want to inspect the formulas
    #print aut
    #set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)
    #print solver
    start_t = default_timer()
    res = _emp_z3.check()
    end_t = default_timer()

    t = end_t - start_t

    _emp_z3.pop()

    return res == unsat

class _Z3NormAutEnc:
    """An object encoding the given normalised automaton in Z3"""

    # delta for sibling arrow
    __delta = Int("dunopt")
    __nvar = Int("nunopt")
    __bvar = Int("bunopt")

    def __init__(self, aut, solver):
        """Constructs a Z3 encoding of aut, adds constraints to solver.

        :param aut:
            A normalised (with _normalise_automaton) CSSAutomaton
        :param solver:
            A Z3 Solver to add the constraints to
        """
        self.aut = aut
        self.solver = solver
        self.last = self.__has_last_constraints()
        self.of_type = self.__has_of_type_constraints()
        # Note, we must have last_of_type => of_type
        self.last_of_type = self.__has_last_of_type_constraints()
        self.has_id = self.__has_id_constraints()
        self.has_target = self.__has_pseudo_elements(set(["target"]))
        self.__setup_z3_variables()
        self.__initial_constraints()
        self.__final_constraints()
        self.__transition_constraints()
        self.__variable_constraints()

    def __nth(self, x, a, b):
        """Returns an existential Presburger clause enforcing

            (E)n . x = an + b

        :param x:
            z3 Int variable
        :param a:
            constant python integer
        :param b:
            constant python integer
        :returns:
            z3 clause enforcing the above
        """
        if a != 0:
            return Exists([self.__nvar], And(self.__nvar >= 0,
                                             x == a * self.__nvar + b))
        else:
            return x == b

    def __not_nth(self, x, a, b):
        """Returns an existential Presburger clause enforcing

            not (E)n . x = an + b

        :param x:
            z3 Int variable
        :param a:
            constant python integer
        :param b:
            constant python integer
        :returns:
            z3 clause enforcing the above
        """
        if a == 0:
            return x != b

        b1 = b // a
        b2 = b % a
        bnd__b2 = (
            (self.__bvar > -abs(a))
            if (a * b1 < 0)
            else (self.__bvar < abs(a))
        )
        dir__b2 = (
            (self.__bvar <= 0)
            if (a * b1 < 0)
            else (self.__bvar >= 0)
        )
        xvsb = (x < b) if a > 0 else (x > b)
        return Or(xvsb,
                  Exists([self.__nvar, self.__bvar],
                         And(bnd__b2,
                             dir__b2,
                             self.__bvar != b2,
                             x == (a*self.__nvar) + (a*b1) + self.__bvar)))

    def __sel_has_pseudo_elements(self, sel, cons, neg_cons = None):
        """Returns true if selector has any of the of type constraints in cons

        :param sel:
            The selector in cssselect parsed_tree format
        :param cons:
            A python set of strings, the strings being the names of pseudo
            elements such as "last-of-type"
        :param neg_cons:
            If specified, then cons will only refer to positive selectors
            and neg_cons will be selectors in :not()
        :returns:
            True iff there is an selector from cons in sel
        """
        if neg_cons is None:
            neg_cons = cons

        s = sel
        while type(s).__name__ != "Element":
            check_sel = s
            check_cons = cons
            if type(s).__name__ == "Negation":
                check_sel = s.subselector
                check_cons = neg_cons
            t = type(check_sel).__name__
            if (t == "Pseudo" and check_sel.ident in check_cons):
                return True
            if (t == "Function" and check_sel.name in check_cons):
                return True
            s = s.selector
        return False

    def __has_pseudo_elements(self, cons):
        """
        :param cons:
            A set of pseudo element / function names as strings
        :returns:
            True iff something from cons appears in a transition of self.aut
        """
        for t in self.aut:
            if self.__sel_has_pseudo_elements(t.node_selector, cons):
                return True
        return False

    def __has_last_constraints(self):
        cons = set(["nth-last-child",
                    "nth-last-of-type",
                    "last-child",
                    "only-child",
                    "last-of-type",
                    "only-of-type"])
        return self.__has_pseudo_elements(cons)

    def __has_of_type_constraints(self):
        """Looks through aut to see if it has any "of type" constraints

        :returns:
            True iff self.aut contains some of type constraints
        """
        return self.__has_pseudo_elements(_of_type_cons)


    def __has_last_of_type_constraints(self):
        """Looks through aut to see if it has any "last of type" constraints

        :returns:
            True iff self.aut contains some of type constraints
        """
        cons = set(["nth-last-of-type",
                    "only-of-type",
                    "last-of-type"])
        return self.__has_pseudo_elements(cons)


    def __has_id_constraints(self):
        """:returns: True iff some transitions contain ID constraints"""
        for t in self.aut:
            if self.__sel_has_id_constraints(t.node_selector):
                return True
        return False

    def __sel_has_id_constraints(self, sel):
        """
        :param sel:
            The selector in cssselect parsed_tree format
        :returns:
            True iff there is an ID in sel e.g.  #i
        """
        s = sel
        while type(s).__name__ != "Element":
            check_sel = s
            if type(s).__name__ == "Negation":
                check_sel = s.subselector
            if (type(check_sel).__name__ == "Hash"):
                return True
            s = s.selector
        return False

    def __setup_z3_variables(self):
        """Creates the variables for the encoding

            n -- the length of the longest run
            qsort -- z3 enum for states
            qvals -- dict from State to z3 values
            qvars -- array of n state variables

            similarly for prefixes (instead of q)

                ns -- namespaces (e.g. nssort)
                e -- elements
                id -- ids

            psvars -- dict from string pseudo element to array of n
                      boolean variables (e.g. psvars["target"][3] for
                      whether 3rd point in run has target)

            nchild, nlchild -- arrays of n Int vars for nth child and
                               nth from last child

            ntchild, nltchild -- dicts from (ns, e) to n Int vars for
                                 tracking how many elements of type where
                                 ns is in nsvals and e in evals

            arrvars -- the arrow on the transition used at each position
            arrvals -- the values as a dict over Arr enum vals
        """

        comps = self.aut.components()

        self.n = comps.num_trans

        self._enum_id = _get_next_enum_id()

        # state variables
        aut_qs = list(comps.states)
        self.qsort, vals = EnumSort(
            "State" + self._enum_id, [q.name for q in aut_qs]
        )
        self.qvals = {}
        for q, v in zip(aut_qs, vals):
            self.qvals[q] = v
        self.qvars = [Const("q" + str(i), self.qsort)
                      for i in range(self.n)]

        # namespace and element variables
        nss = list(comps.namespaces)
        eles = list(comps.elements)
        # add dummies for all transitions that might need them
        i = 0
        nss.append("_null_ns")
        eles.append("_null_ele")
        for t in self.aut:
            (dummy_ns, dummy_ele) = self.__get_tran_dummies(t)
            if dummy_ns:
                nss.append("_dummy_ns" + str(i))
                i += 1
            if dummy_ele:
                eles.append("_dummy_ele" + str(i))
                i += 1

        self.nssort, vals = EnumSort(
            "Namespace" + self._enum_id, list(map(str, nss))
        )
        self.nsvals = {}
        for ns, v in zip(nss, vals):
            self.nsvals[ns] = v
        self.nsvars = [Const("ns" + str(i), self.nssort)
                       for i in range(self.n)]

        self.esort, vals = EnumSort(
            "Element" + self._enum_id, list(map(str, eles))
        )
        self.evals = {}
        for e, v in zip(eles, vals):
            self.evals[e] = v
        self.evars = [Const("e" + str(i), self.esort)
                      for i in range(self.n)]

        if self.has_id:
            ids = list(comps.ids)
            self.dummy_id = "_dummy_id"
            ids.append(self.dummy_id)
            self.idsort, vals = EnumSort(
                "ID2_" + self._enum_id, list(map(str, ids))
            )
            self.idvals = {}
            for i, v in zip(ids, vals):
                self.idvals[i] = v
            self.idvars = [Const("id" + str(i), self.idsort)
                           for i in range(self.n)]

        self.psvars = {}
        for ps in _global_ps:
            self.psvars[ps] = [Bool(ps + str(i)) for i in range(self.n)]

        # nth-child, nth-last-child, and of-type variants
        self.nchild = [Int("n" + str(i)) for i in range(self.n)]
        if self.last:
            self.nlchild = [Int("nl" + str(i)) for i in range(self.n)]
        if self.of_type:
            self.ntchild = {}
            for ns in self.nsvals:
                for e in self.evals:
                    self.ntchild[(ns, e)] = (
                        [Int("nt_" + str(ns) + "_" + str(e) + str(i))
                         for i in range(self.n)]
                    )
        if self.last_of_type:
            self.nltchild = {}
            for ns in self.nsvals:
                for e in self.evals:
                    self.nltchild[(ns, e)] = (
                        [Int("nlt_" + str(ns) + "_" + str(e) + str(i))
                         for i in range(self.n)]
                    )

        # arrow variables
        arrows = [a for a in Arrow]
        self.arrsort, vals = EnumSort(
            "Arrow" + self._enum_id, [str(a) for a in arrows]
        )
        self.arrvals = {}
        for a, v in zip(arrows, vals):
            self.arrvals[a] = v
        self.arrvars = [Const("a" + str(i), self.arrsort)
                        for i in range(self.n)]



    def __get_tran_dummies(self, t):
        """
        :param t:
            A transition Tran
        :returns:
            (dummy_ns, dummy_ele)
            where dummy_ns is True iff transition implies need for a dummy namespace
            and dummy_ele is True iff transition implies need for a dummy element
        """
        sel = t.node_selector

        # if selector is just * no dummy required
        if (type(sel).__name__ == "Element" and
            sel.namespace is None and
            sel.element is None):
            return (False, False)

        # else find if it forces namespace or element, and if it has an of-type
        # requirement
        is_of_type = self.__sel_has_pseudo_elements(sel, _of_type_cons)

        if not is_of_type:
            return (False, False)

        while type(sel).__name__ != "Element":
            sel = sel.selector

        if sel.namespace == None:
            return (True, False)
        elif sel.element == None:
            return (False, True)
        else:
            return (False, False)

    def __variable_constraints(self):
        """Adds consistency constraints on the variables to solver.
           E.g. nchild > 0 and nchild is sumof ntchild, all IDs unique...
        """
        # > 0
        for v in self.nchild:
            self.solver.append(v > 0)
        if self.last:
            for v in self.nlchild:
                self.solver.append(v > 0)
        # of type can be 0 too
        if self.of_type:
            for vs in self.ntchild.values():
                for v in vs:
                    self.solver.append(v >= 0)
            # nchild = sum of ntchild
            for i in range(self.n):
                self.solver.append(self.nchild[i]
                                   ==
                                   Sum([vs[i] for vs in self.ntchild.values()]))

        if self.last_of_type:
            for vs in self.nltchild.values():
                for v in vs:
                    self.solver.append(v >= 0)
            # nlchild = sum of nltchild
            for i in range(self.n):
                self.solver.append(self.nlchild[i]
                                   ==
                                   Sum([vs[i] for vs in self.nltchild.values()]))

        # unique target and IDs
        for i in range(self.n):
            id_cons = []
            for j in range(i + 1, self.n):
                if self.has_id:
                    id_cons.append(self.idvars[i] != self.idvars[j])
                if self.has_target:
                    self.solver.append(Not(And(self.psvars["target"][i],
                                               self.psvars["target"][j])))
            if self.has_id:
                self.solver.append(Or(self.idvars[i] == self.idvals[self.dummy_id],
                                      And(id_cons)))

        # if a node is not root, the next visited note cannot be root either
        for i in range(self.n - 1):
            self.solver.append(Implies(Not(self.psvars["root"][i]),
                                       Not(self.psvars["root"][i+1])))

    def __initial_constraints(self):
        """Z3 encoding of constraints on the initial variable assignment (0th pos)
        added to self.solver
        """
        self.solver.append(self.qvars[1] == self.qvals[self.aut.qinit])
        self.solver.append(self.__first_child_cons(0))
        self.solver.append(self.psvars["root"][0])


    def __final_constraints(self):
        """Z3 encoding of constraints saying a run has ended added to self.solver
        """
        self.solver.append(self.qvars[self.n - 1] == self.qvals[self.aut.qfinal])

    def __transition_constraints(self):
        """Z3 encoding of transition relation added to self.solver
        """
        # Strategy:
        #
        #   Work out which states can appear at a position in the run.
        #   states[i] is the set of states at position i, with a flag to say if
        #   it was added because of a loop.

        #   Initially states[0] = {q0}
        #             no_loop = {(0, q0)}
        #
        #   Then, for each q1 --> q2, put q2 in the next position.
        #   For loops, since we can only take a loop once, we deal with the
        #   separately: if q in states[i] and (i, q) in no_loop, and there are k
        #   loops, add q to states[i+1..i+k].
        #
        #   Treat non-loops q1 --> q2 obviously q1 in states[i] leads to
        #   q2 in states[i+1] and (i+1, q2) in no_loop.
        states = defaultdict(set)
        states[0] = set([self.aut.qinit])
        no_loop = set([(0, self.aut.qinit)])

        for i in range(self.n - 1):
            tran_opts = [self.qvars[i] == self.qvals[self.aut.qfinal]]
            arrows = set([])

            for q in states[i]:
                loop_dist = 1
                for t in self.aut.trans_from(q):
                    tran_opts.append(self.__tran_pres(t, i))
                    arrows.add(t.arrow)
                    if t.q1 != t.q2 and i < self.n - 1:
                        states[i+1].add(t.q2)
                        no_loop.add((i+1, t.q2))
                    elif (i, q) in no_loop:
                        if i + loop_dist < self.n:
                            states[i + loop_dist].add(q)
                            loop_dist += 1

            self.solver.append(Or(tran_opts))

            for arr in arrows:
                next_vals = {
                    Arrow.child : lambda : self.__arr_child_pres(i),
                    Arrow.neighbour : lambda : self.__arr_neighbour_pres(i),
                    Arrow.sibling : lambda : self.__arr_sibling_pres(i),
                    Arrow.noop : lambda : self.__arr_noop_pres(i)
                }[arr]()
                self.solver.append(Implies(
                    self.arrvars[i] == self.arrvals[arr],
                    next_vals
                ))


    def _test_sel_pres(self, sel, i):
        """Non-private access to __sel_pres for testing purposes"""
        return self.__sel_pres(sel, i)

    def __sel_pres(self, sel, i):
        """Encodes the node selector sel for the ith position of the run.

        :param sel:
            The (normalised) node selector in cssselect parsed_tree format
        :param i:
            The position in the run to build the formula for
        :returns:
            A Z3 formula encoding that the selector is true at the node
            at position i of the run
        """
        cons = []
        stype = type(sel).__name__
        if stype == "Element":
            if sel.namespace is not None:
                cons.append(self.nsvars[i] == self.nsvals[sel.namespace])
            if sel.element is not None:
                cons.append(self.evars[i] == self.evals[sel.element])
        else:
            cons.append(self.__sel_pres(sel.selector, i))
            if stype == "Negation":
                cons.append(self.__sel_pres_neg(sel.subselector, i))
            elif stype == "Hash":
                cons.append(self.idvars[i] == self.idvals[sel.id])
            elif stype == "Pseudo":
                if sel.ident == "first-child":
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth(self.nchild[i], 0, 1))
                elif sel.ident == "last-child":
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth(self.nlchild[i], 0, 1))
                elif sel.ident == "only-child":
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth(self.nchild[i], 0, 1))
                    cons.append(self.__nth(self.nlchild[i], 0, 1))
                elif sel.ident == "first-of-type":
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth_of_type(0, 1, i))
                elif sel.ident == "last-of-type":
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth_last_of_type(0, 1, i))
                elif sel.ident == "only-of-type":
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth_of_type(0, 1, i))
                    cons.append(self.__nth_last_of_type(0, 1, i))
                else:
                    cons.append(self.psvars[sel.ident][i])
            elif stype == "Function":
                if sel.name == "nth-child":
                    a, b = cssfile.get_fun_sel_coefs(sel)
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth(self.nchild[i], a, b))
                elif sel.name == "nth-last-child":
                    a, b = cssfile.get_fun_sel_coefs(sel)
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth(self.nlchild[i], a, b))
                elif sel.name == "nth-of-type":
                    a, b = cssfile.get_fun_sel_coefs(sel)
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth_of_type(a, b, i))
                elif sel.name == "nth-last-of-type":
                    a, b = cssfile.get_fun_sel_coefs(sel)
                    cons.append(Not(self.psvars["root"][i]))
                    cons.append(self.__nth_last_of_type(a, b, i))
                else:
                    raise AutEmptinessException("Unrecognised function selector " +
                                                str(sel))
        return And(cons)

    def __sel_pres_neg(self, sel, i):
        """Encodes the negation of node selector sel for the ith position
        of the run.

        :param sel:
            The (normalised) node selector in cssselect parsed_tree format
        :param i:
            The position in the run to build the formula for
        :returns:
            A Z3 formula encoding that the selector is false at the node
            at position i of the run
        """
        stype = type(sel).__name__
        if stype == "Element":
            if (sel.namespace is None and
                sel.element is None):
                return Or() # FALSE

            if sel.namespace is not None:
                return Or(self.nsvars[i] != self.nsvals[sel.namespace])
            if sel.element is not None:
                return Or(self.evars[i] != self.evals[sel.element])
        elif stype == "Pseudo":
            if sel.ident == "first-child":
                return Or(self.psvars["root"][i],
                          self.__not_nth(self.nchild[i], 0, 1))
            elif sel.ident == "last-child":
                return Or(self.psvars["root"][i],
                          self.__not_nth(self.nlchild[i], 0, 1))
            elif sel.ident == "only-child":
                return Or(
                    self.psvars["root"][i],
                    self.__not_nth(self.nchild[i], 0, 1),
                    self.__not_nth(self.nlchild[i], 0, 1)
                )
            elif sel.ident == "fist-of-type":
                return Or(self.psvars["root"][i],
                          self.__not_nth_of_type(0, 1, i))
            elif sel.ident == "last-of-type":
                return Or(self.psvars["root"][i],
                          self.__not_nth_last_of_type(0, 1, i))
            elif sel.ident == "only-of-type":
                return Or(
                    self.psvars["root"][i],
                    self.__not_nth_of_type(0, 1, i),
                    self.__not_nth_last_of_type(0, 1, i)
                )
            else:
                return Not(self.psvars[sel.ident][i])
        elif stype == "Function":
            if sel.name == "nth-child":
                a, b = cssfile.get_fun_sel_coefs(sel)
                return Or(self.psvars["root"][i],
                          self.__not_nth(self.nchild[i], a, b))
            elif sel.name == "nth-last-child":
                a, b = cssfile.get_fun_sel_coefs(sel)
                return Or(self.psvars["root"][i],
                          self.__not_nth(self.nlchild[i], a, b))
            elif sel.name == "nth-of-type":
                a, b = cssfile.get_fun_sel_coefs(sel)
                return Or(self.psvars["root"][i],
                          self.__not_nth_of_type(a, b, i))
            elif sel.name == "nth-last-of-type":
                a, b = cssfile.get_fun_sel_coefs(sel)
                return Or(self.psvars["root"][i],
                          self.__not_nth_last_of_type(a, b, i))
            else:
                raise AutEmptinessException("Unrecognised function selector " +
                                            str(sel))
    def __nth_of_type(self, a, b, i):
        """Constructs a clause expressing the same as the selector of
        the same name.  an + b for the ith position in the run.

        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :param i:
            Index in the run to construct the clause for
        :returns:
            Z3 encoding expressing the selector
        """
        return self.__of_type(a, b, i, self.ntchild, self.__nth)

    def __not_nth_of_type(self, a, b, i):
        """Constructs a clause expressing the same as the selector of
        the same name, but negated.  Not an + b for the ith position in
        the run.

        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :param i:
            Index in the run to construct the clause for
        :returns:
            Z3 encoding expressing the selector
        """
        return self.__of_type(a, b, i, self.ntchild, self.__not_nth)

    def __nth_last_of_type(self, a, b, i):
        """Constructs a clause expressing the same as the selector of
        the same name.  an + b for the ith position in the run.

        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :param i:
            Index in the run to construct the clause for
        :returns:
            Z3 encoding expressing the selector
        """
        return self.__of_type(a, b, i, self.nltchild, self.__nth)

    def __not_nth_last_of_type(self, a, b, i):
        """Constructs a clause expressing the same as the selector of
        the same name, but negated.  Not an + b for the ith position in
        the run.

        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :param i:
            Index in the run to construct the clause for
        :returns:
            Z3 encoding expressing the negated selector
        """
        return self.__of_type(a, b, i, self.nltchild, self.__not_nth)


    def __of_type(self, a, b, i, pos_vars, pos_fun):
        """Constructs a clause expressing the node at position i in
        the run is an + bth of type, according to pos_fun

        :param a:
            Integer multiple of n
        :param b:
            Integer offset
        :param i:
            Index in the run to construct the clause for
        :param pos_vars:
            either self.ntchild or self.nltchild
        :param pos_fun:
            self.__nth or self.__not_nth
        :returns:
            Z3 encoding expressing the selector
        """
        choices = []
        for ns in self.nsvals:
            for e in self.evals:
                choices.append(
                    And(
                        self.nsvars[i] == self.nsvals[ns],
                        self.evars[i] == self.evals[e],
                        pos_fun(pos_vars[(ns, e)][i], a, b)
                    )
                )
        return Or(choices)

    def __tran_pres(self, t, i):
        """Encodes the effect of transition t from position i to i+1 as a z3 formula,
        only asserts that the arrow variable for the transition is true.  Constraints
        enforcing how arrow a used at position i effects the position variable values
        for i+1 have to be encoding externally.

        :param t:
            The Tran to encode
        :param i:
            The position in the run the transition leaves from
        :returns:
            A Z3 constraint expressing the effect of the transition
        """
        if i < 0 or i >= self.n:
            raise AutEmptinessException("Position to __tran_pres too high (i = " +
                                        i +
                                        ")")
        cons = []

        # States
        cons.append(self.qvars[i] == self.qvals[t.q1])
        cons.append(self.qvars[i+1] == self.qvals[t.q2])

        # Node selector satisfied
        cons.append(self.__sel_pres(t.node_selector, i))

        # Specific constraints to arrow type
        cons.append(self.arrvars[i] == self.arrvals[t.arrow])

        return And(cons)

    def __arr_child_pres(self, i):
        """Encodes the effect of child transition from position i to i+1 as a z3
        formula.

        :param i:
            The position in the run the transition leaves from, must be < n - 1
        :returns:
            A Z3 constraint expressing the effect of the transition
        """
        cons = []

        # Needs children
        cons.append(Not(self.psvars["empty"][i]))
        # Position info of next node
        cons.append(self.__first_child_cons(i+1))

        return And(cons)

    def __arr_neighbour_pres(self, i):
        """Encodes the effect of neighbour transition t from position i to i+1
        as a z3 formula.

        :param i:
            The position in the run the transition leaves from, must be < n - 1
        :returns:
            A Z3 constraint expressing the effect of the transition
        """
        cons = [Not(self.psvars["root"][i])]

        cons.append(self.nchild[i+1] == self.nchild[i] + 1)
        if self.last:
            cons.append(self.nlchild[i+1] == self.nlchild[i] - 1)

        # Here we use last_of_type => of_type
        if self.of_type:
            for ns in self.nsvals:
                for e in self.evals:
                    n_ns_e = self.ntchild[(ns, e)][i]
                    n_ns_e_p = self.ntchild[(ns, e)][i+1]
                    if not self.last_of_type:
                        cons.append(If(And(self.nsvars[i+1] == self.nsvals[ns],
                                           self.evars[i+1] == self.evals[e]),
                                       n_ns_e_p == n_ns_e + 1,
                                       n_ns_e_p == n_ns_e))
                    else:
                        nl_ns_e = self.nltchild[(ns, e)][i]
                        nl_ns_e_p = self.nltchild[(ns, e)][i+1]
                        cons.append(If(And(self.nsvars[i+1] == self.nsvals[ns],
                                           self.evars[i+1] == self.evals[e]),
                                       And(n_ns_e_p == n_ns_e + 1,
                                           nl_ns_e_p == nl_ns_e - 1),
                                       And(n_ns_e_p == n_ns_e,
                                           nl_ns_e_p == nl_ns_e)))

        return And(cons)

    def __arr_sibling_pres(self, i):
        """Encodes the effect of a sibling transition from position i to i+1 as
        a z3 formula.

        :param i:
            The position in the run the transition leaves from, must be < n - 1
        :returns:
            A Z3 constraint expressing the effect of the transition
        """
        cons = [Not(self.psvars["root"][i])]

        if not self.last:
            cons.append(Exists(
                [self.__delta],
                And(self.__delta >= 1,
                    self.nchild[i+1] == self.nchild[i] + self.__delta)
            ))
        else:
            cons.append(Exists(
                [self.__delta],
                And(self.__delta >= 1,
                    self.nchild[i+1] == self.nchild[i] + self.__delta,
                    self.nlchild[i+1] == self.nlchild[i] - self.__delta)
            ))

        # Here we use last_of_type => of_type
        if self.of_type:
            for ns in self.nsvals:
                for e in self.evals:
                    n_ns_e = self.ntchild[(ns, e)][i]
                    n_ns_e_p = self.ntchild[(ns, e)][i+1]
                    if not self.last_of_type:
                        cons.append(Exists(
                            [self.__delta],
                            And(self.__delta >= 0,
                                If(And(self.nsvars[i+1] == self.nsvals[ns],
                                       self.evars[i+1] == self.evals[e]),
                                   n_ns_e_p == n_ns_e + self.__delta + 1,
                                   n_ns_e_p == n_ns_e + self.__delta))
                        ))
                    else:
                        nl_ns_e = self.nltchild[(ns, e)][i]
                        nl_ns_e_p = self.nltchild[(ns, e)][i+1]
                        cons.append(Exists(
                            [self.__delta],
                            And(self.__delta >= 0,
                                If(And(self.nsvars[i+1] == self.nsvals[ns],
                                       self.evars[i+1] == self.evals[e]),
                                   And(n_ns_e_p == n_ns_e + self.__delta + 1,
                                       nl_ns_e_p == nl_ns_e - self.__delta - 1),
                                   And(n_ns_e_p == n_ns_e + self.__delta,
                                       nl_ns_e_p == nl_ns_e - self.__delta)))
                        ))

        return And(cons)

    def __arr_noop_pres(self, i):
        """Encodes the effect of noop transition from position i to i+1 as a z3
        formula.

        :param i:
            The position in the run the transition leaves from, must be < n - 1
        :returns:
            A Z3 constraint expressing the effect of the transition
        """
        cons = []

        cons.append(self.nchild[i+1] == self.nchild[i])
        if self.last:
            cons.append(self.nlchild[i+1] == self.nlchild[i])

        # Here we use last_of_type => of_type
        if self.of_type:
            for ns in self.nsvals:
                for e in self.evals:
                    n_ns_e = self.ntchild[(ns, e)][i]
                    n_ns_e_p = self.ntchild[(ns, e)][i+1]
                    cons.append(n_ns_e_p == n_ns_e)
                    if self.last_of_type:
                        nl_ns_e = self.nltchild[(ns, e)][i]
                        nl_ns_e_p = self.nltchild[(ns, e)][i+1]
                        cons.append(nl_ns_e_p == nl_ns_e)

        return And(cons)

    def __first_child_cons(self, i):
        """A constraint insisting that the ith position contains the first child.
        That is, ni = 1, and the of-type variables match the type of the node.

        :param i:
            The position in the run (integer)
        :returns:
            A Z3 encoding that the ith position contains a first child.
        """
        cons = []

        cons.append(self.nchild[i] == 1)
        if self.of_type:
            for ns in self.nsvals:
                for e in self.evals:
                    n_ns_e = self.ntchild[(ns, e)][i]
                    cons.append(If(And(self.nsvars[i] == self.nsvals[ns],
                                       self.evars[i] == self.evals[e]),
                                   n_ns_e == 1,
                                   n_ns_e == 0))
        return And(cons)

