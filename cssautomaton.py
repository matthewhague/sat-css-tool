
"""Representation of a CSS automaton and functions to build from a selector"""

import re
import copy
from enum import Enum
from collections import defaultdict

import cssselect_parser
from cssselect_parser import Element
from lxml import etree
# yeah -- using two cssselector libraries, but one has the AST the other does
# matching...
from lxml.cssselect import CSSSelector

import cssfile

# * selector for convenience
_isany = cssselect_parser.parse("*").pop().parsed_tree

# regular expression for parsing transitions
_tranRE = re.compile("(\w*) -- ([csn0]), (.*) --> (\w*)")
_q1grp = 1
_arrgrp = 2
_nsgrp = 3
_q2grp = 4


class CSSAutConstructionException(Exception):
    pass

def fromstring(cssstring, namespaces = {}):
    """Build a CSSAutomaton from a CSS string

    :param cssstring:
        The CSS string to build the automaton from.
    :param namespaces:
        A dict of 'namespace' : 'uri' pairs to use for selector evaluation
    :returns:
        A CSSAutomaton representing the given CSS
    """
    css = cssselect_parser.parse(cssstring).pop().parsed_tree
    return fromselector(css, namespaces)

def fromselector(css, namespaces = {}):
    """Build a CSSAutomaton from a cssselect selector (parsed tree)

    :param css:
        The cssselect selector to build the automaton from.
    :param namespaces:
        A dict of 'namespace' : 'uri' pairs to use for selector evaluation
    :returns:
        A CSSAutomaton representing the given CSS
    """
    aut = CSSAutomaton(namespaces)
    aut.qinit = aut._new_state()
    aut.qfinal = aut._new_state()
    aut.add_tran(Tran(aut.qinit, Arrow.child, _isany, aut.qinit))
    aut.add_tran(Tran(aut.qinit, Arrow.sibling, _isany, aut.qinit))
    __build_aut_from_selector(aut, css, aut.qinit, aut.qfinal, Combinator.noop)
    return aut

def fromlist(slist):
    """Takes a list where the first two items are strings giving the name of
    qinit and qfinal respectively, and the remaining items are string
    representations of transitions

        q1 -- {c, n, s, 0}, <selector> --> q2

    where c is child, n neighbour, s sibling, and 0 noop.
    Adds the transitions to the automaton.

    :param trans:
        list of strings, where the first two are the init and final states
        and the rest represent transitions
    """
    aut = CSSAutomaton()
    aut.qinit = State(slist[0])
    aut.qfinal = State(slist[1])
    for t in slist[2:]:
        m = _tranRE.match(t)
        if m is None:
            raise CSSAutConstructionException("Unparsable transition" + t)
        css = cssselect_parser.parse(m.group(_nsgrp)).pop().parsed_tree
        arr = {
            "c" : Arrow.child,
            "n" : Arrow.neighbour,
            "s" : Arrow.sibling,
            "0" : Arrow.noop
        }[m.group(_arrgrp)]
        aut.add_tran(Tran(State(m.group(_q1grp)),
                          arr,
                          css,
                          State(m.group(_q2grp))))
    return aut

def intersect(aut1, aut2):
    """Forms the intersection of two CSSAutomaton objects.
    Throws exception if namespaces of both automata are not the same.

    :param css1:
        A CSSAutomaton, the first operand of the intersection
    :param css2:
        A CSSAutomaton, the second operand of the intersection
    :returns:
        A CSSAutomaton that is the intersection of the two
    """
    if (aut1.namespaces != aut2.namespaces):
        raise CSSAutConstructionException("Can only intersect automata with matching namespaces.")
    aut = CSSAutomaton(aut1.namespaces)
    aut.qinit = _product_states(aut1.qinit, aut2.qinit)
    aut.qfinal = _product_states(aut1.qfinal, aut2.qfinal)
    for t1 in aut1:
        for t2 in aut2:
            t = _product_trans(t1, t2)
            if t is not None:
                aut.add_tran(t)
    return aut


class State:
    """A state of a CSS automaton"""
    def __init__(self, name):
        """:param name:
                the name of the state as a string
        """
        self.name = name

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.name == other.name
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __str__(self):
        return self.name

    def __repr__(self):
        return str(self) + "<" + repr(id(self)) + ">"

    def __hash__(self):
        return hash(self.name)


class Arrow(Enum):
    """The kinds of directional arrows that can label transitions"""
    child = 1
    neighbour = 2
    sibling = 3
    noop = 4

    def __str__(self):
        if (self == Arrow.child):
            return ">"
        elif (self == Arrow.neighbour):
            return "+"
        elif (self == Arrow.sibling):
            return "~"
        elif (self == Arrow.noop):
            return "."

class Combinator(Enum):
    child = 1
    descendant = 2
    neighbour = 3
    sibling = 4
    noop = 5
    def __str__(self):
        if (self == Combinator.child):
            return ">"
        if (self == Combinator.descendant):
            return ">>"
        elif (self == Combinator.neighbour):
            return "+"
        elif (self == Combinator.sibling):
            return "~"
        elif (self == Combinator.noop):
            return "."

class Tran:
    """A generic CSS automaton transition"""
    def __init__(self, q1, arrow, node_selector, q2):
        """:param q1:
                The source state (as State)
           :param arrow:
                The type of arrow labelling the transition (as Arrow)
           :param node_selector:
                A cssselect selector with no sibling or descendant combinators
           :param q2:
                The target state (as State)
        """
        self.q1 = q1
        self.arrow = arrow
        self.node_selector = node_selector
        self.q2 = q2

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            # the use of str is a bit of a hack, but if the cssselect library
            # didn't implement __eq__...
            return (self.q1 == other.q1 and
                    self.arrow == other.arrow and
                    str(self.node_selector) == str(other.node_selector) and
                    self.q2 == other.q2)
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return (hash(self.q1) +
                hash(self.arrow) +
                # all our transitions will be unique by q1, arrow q2 anyhow
                #hash(self.node_selector) +
                hash(self.q2))

    def __str__(self):
        return (str(self.q1) +
                "-- " +
                str(self.arrow) +
                ", " +
                str(self.node_selector) +
                " --> " +
                str(self.q2))

class CSSComponents:
    """A class to hold information about a CSSAutomaton:

        num_trans -- the number of transitions in the automaton
        states -- the set of states as State
        namespaces -- the set of namespaces as Strings appearing in the
                      selectors
        elements -- the set of elements as Strings appearing in the
                    selectors
        ids -- the set of ids as strings appearing in the selectors
    """
    def __init__(self):
        self.states = set([])
        self.namespaces = set([])
        self.elements = set([])
        self.ids = set([])

class CSSAutomaton:
    _nextstate = 0

    def __init__(self, namespaces = {}):
        """An empty CSS automaton

        :param namespaces:
            A dict of 'namespace' : 'uri' pairs to use in selector evaluation
        """
        # map from q to trans to q
        self.trans = defaultdict(set)
        # map from q to trans from q
        self.trans_fwd = defaultdict(set)
        self.namespaces = namespaces
        self.qinit = None
        self.qfinal = None

    def add_tran(self, tran):
        """Add a new transition to the automaton

        :param tran:
            The new transition as a Tran
        """
        self.trans[tran.q2].add(tran)
        self.trans_fwd[tran.q1].add(tran)

    def trans_from(self, q):
        """Returns the set of transitions from a given state.

        :param q:
            The State to get the transitions from.
        :returns:
            The set of transitions (as Tran) from q
        """
        return self.trans_fwd[q]

    def accepts(self, node):
        """Detects if the node of an XML document is accepted by the automaton.
        The CSS matching in this method is quite inefficient, so probably only
        really good for testing purposes (but that's all we need it for anyway).

        :param node:
            The node to test, as a Element from etree in lxml
        :returns:
            True iff the node is accepted
        """
        # worklist of (node, state) pairs, repeat until empty or we find
        # (root, init)
        worklist = set([(node, self.qfinal)])
        donelist = set([])
        while len(worklist) > 0:
            (n, q) = worklist.pop()
            donelist.add((n, q))
            for t in self.trans[q]:
                next_n = None
                next_q = t.q1

                if t.arrow == Arrow.child:
                    next_n = n.getparent()
                elif t.arrow == Arrow.neighbour:
                    next_n = n.getprevious()
                elif t.arrow == Arrow.sibling:
                    next_n = n.getprevious()
                    next_q = t.q2
                elif t.arrow == Arrow.noop:
                    next_n = n

                # this seems quite inefficient... (esp getroottree...)
                matcher = CSSSelector(cssfile.selector_str_pt(t.node_selector),
                                      namespaces=self.namespaces)
                if next_n is not None and next_n in matcher(next_n.getroottree()):
                    if (next_n.getparent() is None and
                        next_q == self.qinit):
                        return True
                    elif not (next_n, next_q) in donelist:
                        worklist.add((next_n, next_q))
        return False

    def components(self):
        """This method computes the sets of components on each call.

        :returns:
            A completed CSSAutomatonComponents object for the aut
        """
        comps = CSSComponents()
        comps.num_trans = sum([len(ts) for ts in self.trans.values()])
        comps.states.add(self.qinit)
        comps.states.add(self.qfinal)
        for t in self:
            comps.states.add(t.q1)
            comps.states.add(t.q2)
            sel = t.node_selector
            while True:
                s = (sel if type(sel).__name__ != "Negation"
                         else sel.subselector)

                stype = type(s).__name__
                if stype == "Element":
                    if s.namespace is not None:
                        comps.namespaces.add(s.namespace)
                    if s.element is not None:
                        comps.elements.add(s.element)
                elif stype == "Hash":
                    comps.ids.add(s.id)

                # move on or finish
                if type(sel).__name__ == "Element":
                    break

                sel = sel.selector
        return comps

    # only weakly protected so test.py can use it
    def _new_state(self):
        """Returns a fresh state, for use in automaton construction"""
        state = State("q" + str(self._nextstate))
        self._nextstate += 1
        return state

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return (self.qinit == other.qinit and
                    self.qfinal == other.qfinal and
                    self.namespaces == other.namespaces and
                    self.trans == other.trans)
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __str__(self):
        lines = ["Init: " + str(self.qinit),
                 "Final: " + str(self.qfinal),
                 "Namespaces: " + str(self.namespaces),
                 ""]
        for t in self:
            lines.append("  " + str(t))
        return '\n'.join(lines)

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __iter__(self):
        """iterates over Tran-s of automaton"""
        for _, ts in self.trans.items():
            for t in ts:
                yield t

def __build_aut_from_selector(aut, selector, qin, qout, combinator):
    """Fills in the aut object with transitions to represent selector, recursive.
    Does not add transitions to navigate from root to any node in tree.

    :param aut:
        A CSSAutomaton to add the transitions to
    :param selector:
        A Selector object from cssselect
    :param qin:
        A State from which any new transitions will be added
    :param qout:
        A State to exit to after the automaton for selector is done
    :param combinator:
        A Combinator that says how to get from the given selector to the one
        immediately after (next selector not given as an argument) (i.e. how
        to reach qout)
    """
    stype = type(selector).__name__
    if stype == "CombinedSelector":
        qmid = aut._new_state()
        new_combinator = {
            ">" : Combinator.child,
            " " : Combinator.descendant,
            "+" : Combinator.neighbour,
            "~" : Combinator.sibling
            }[selector.combinator]
        __build_aut_from_selector(aut,
                                  selector.selector,
                                  qin,
                                  qmid,
                                  new_combinator)
        qstart = qmid
        node_selector = selector.subselector
    else:
        qstart = qin
        node_selector = selector

    if combinator == Combinator.child:
        aut.add_tran(Tran(qstart, Arrow.child, node_selector, qout))
        qloop = aut._new_state()
        aut.add_tran(Tran(qstart, Arrow.child, node_selector, qloop))
        aut.add_tran(Tran(qloop, Arrow.sibling, _isany, qloop))
        aut.add_tran(Tran(qloop, Arrow.neighbour, _isany, qout))
    elif combinator == Combinator.descendant:
        aut.add_tran(Tran(qstart, Arrow.child, node_selector, qout))
        qloop = aut._new_state()
        aut.add_tran(Tran(qstart, Arrow.child, node_selector, qloop))
        aut.add_tran(Tran(qloop, Arrow.sibling, _isany, qloop))
        aut.add_tran(Tran(qloop, Arrow.child, _isany, qloop))
        aut.add_tran(Tran(qloop, Arrow.neighbour, _isany, qout))
        aut.add_tran(Tran(qloop, Arrow.child, _isany, qout))
    elif combinator == Combinator.neighbour:
        aut.add_tran(Tran(qstart, Arrow.neighbour, node_selector, qout))
    elif combinator == Combinator.sibling:
        aut.add_tran(Tran(qstart, Arrow.neighbour, node_selector, qout))
        qloop = aut._new_state()
        aut.add_tran(Tran(qstart, Arrow.neighbour, node_selector, qloop))
        aut.add_tran(Tran(qloop, Arrow.sibling, _isany, qloop))
        aut.add_tran(Tran(qloop, Arrow.neighbour, _isany, qout))
    elif combinator == Combinator.noop:
        aut.add_tran(Tran(qstart, Arrow.noop, node_selector, qout))
    else:
        raise CSSAutConstructionException("Unrecognised combinator '" +
                                          combinator +
                                          "'")
def _product_states(q1, q2):
    """Form the product of q1 and q2

    :param q1:
        The first State
    :param q2:
        The second State
    :returns:
        A State for q1xq2
    """
    return State("(" + q1.name + "," + q2.name + ")")

def _product_trans(t1, t2):
    """Form the product of t1 and t2

    :param t1:
        The first Tran
    :param t2:
        The second Tran
    :returns:
        A new Tran that is the intersection of t1 and t2 or None if
        the transitions aren't compatible
    """
    q1 = _product_states(t1.q1, t2.q1)
    q2 = _product_states(t1.q2, t2.q2)
    node_selector = _product_selectors(t1.node_selector,
                                       t2.node_selector)
    if node_selector is None:
        return None

    if t1.arrow == t2.arrow:
        return Tran(q1, t1.arrow, node_selector, q2)
    elif t1.arrow == Arrow.neighbour and t2.arrow == Arrow.sibling:
        return Tran(q1, Arrow.neighbour, node_selector, q2)
    elif t1.arrow == Arrow.sibling and t2.arrow == Arrow.neighbour:
        return Tran(q1, Arrow.neighbour, node_selector, q2)
    else:
        return None

def _product_selectors(sel1, sel2):
    """Form the product of two cssselect selectors for a single node (i.e. no >, ,+,~)

    :param sel1:
        The first selector, as a cssselect object (parsed tree)
    :param sel2:
        The second selector, as a cssselect object (parsed tree)
    :returns:
        A cssselect parsed tree that is the intersection of the two, or
        None if incompatible
    """
    stype1 = type(sel1).__name__
    if stype1 == "Element":
        stype2 = type(sel2).__name__
        if stype2 == "Element":
            return _product_element_selectors(sel1, sel2)
        else:
            childprod = _product_selectors(sel2.selector, sel1)
            if childprod is None:
                return None
            else:
                sel = copy.copy(sel2)
                sel.selector = childprod
                return sel
    else:
        childprod = _product_selectors(sel1.selector, sel2)
        if childprod is None:
            return None
        else:
            sel = copy.copy(sel1)
            sel.selector = childprod
            return sel

def _product_element_selectors(ele1, ele2):
    """Returns the product of two cssselector Element objects

    :param ele1:
        The first Element object
    :param ele2:
        The second Element object
    :returns:
        An Element that is the intersection of the two, or None if incompatible
    """
    namespace = None
    if (ele1.namespace == ele2.namespace):
        namespace = ele1.namespace
    elif (ele1.namespace is None and ele2.namespace is not None):
        namespace = ele2.namespace
    elif (ele1.namespace is not None and ele2.namespace is None):
        namespace = ele1.namespace
    else:
        return None

    element = None
    if (ele1.element == ele2.element):
        element = ele1.element
    elif (ele1.element is None and ele2.element is not None):
        element = ele2.element
    elif (ele1.element is not None and ele2.element is None):
        element = ele1.element
    else:
        return None

    return Element(namespace, element)
