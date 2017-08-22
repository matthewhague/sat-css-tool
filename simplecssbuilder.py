"""Functions for constructing from s CSSFile a simpleCSS object for minimisation
purposes"""

from itertools import combinations
from timeit import default_timer

import cssfile
from cssfile import CSSFile
from simpleCSS import *
import cssautomaton
import autemptiness
from cliqueCSS import *
import cssselect_parser

__DEBUG__ = True

numchecks = 0
numpositive = 0
numnontrivialchecks = 0
numpositivenontrivial = 0


SHORTHAND_REL = { "background": ["background-image",
                                 "background-position",
                                 "background-size",
                                 "background-repeat",
                                 "background-origin",
                                 "background-clip",
                                 "background-attachment",
                                 "background-color"],
                   "font": ["font-style",
                            "font-variant",
                            "font-weight",
                            "font-stretch",
                            "font-size",
                            "line-height",
                            "font-family"],
                  "margin": ["margin-bottom",
                             "margin-left",
                             "margin-right",
                             "margin-top"],
                  "border": ["border-top-width",
                             "border-right-width",
                             "border-bottom-width",
                             "border-left-width",
                             "border-style",
                             "border-top-style",
                             "border-right-style",
                             "border-bottom-style",
                             "border-left-style",
                             "border-color",
                             "border-top-color",
                             "border-right-color",
                             "border-bottom-color",
                             "border-left-color"],
                  "border-top": ["border-top-width",
                                 "border-top-style",
                                 "border-top-color"],
                  "border-bottom": ["border-bottom-width",
                                    "border-bottom-style",
                                    "border-bottom-color"],
                  "border-left": ["border-left-width",
                                  "border-left-style",
                                  "border-left-color"],
                  "border-right": ["border-right-width",
                                   "border-right-style",
                                   "border-right-color"],
                  "border-width": ["border-top-width",
                                   "border-right-width",
                                   "border-bottom-width",
                                   "border-left-width"],
                  "border-color": ["border-top-color",
                                   "border-right-color",
                                   "border-bottom-color",
                                   "border-left-color"],
                  "border-style": ["border-top-style",
                                   "border-right-style",
                                   "border-bottom-style",
                                   "border-left-style"],
                  "border-radius": ["border-top-left-radius",
                                    "border-top-right-radius",
                                    "border-bottom-right-radius",
                                    "border-bottom-left-radius"],
                  "transition": ["transition-delay",
                                 "transition-duration",
                                 "transition-property",
                                 "transition-timing-function"],
                  "animation": ["animation-name",
                                "animation-duration",
                                "animation-timing-function",
                                "animation-delay",
                                "animation-iteration-count",
                                "animation-direction",
                                "animation-fill-mode",
                                "animation-play-state"],
                  "padding": ["padding-bottom",
                              "padding-left",
                              "padding-right",
                              "padding-top"],
                  "list-style": ["list-style-type",
                                 "list-style-position",
                                 "list-style-image"] }

def related_props(p1, p2):
    """
    :param p1:
        A property name as a string
    :param p2:
        A property name as a string
    :returns:
        True if property names are related.  That is, p1 = p2, or p1 is
        a shorthand covering p2 or vice versa, or if both can set the
        same value.  E.g. font and font-weight are related and we should
        be mindful of their ordering.
    """
    if p1 == p2:
        return True
    if p1 in SHORTHAND_REL:
        if p2 in SHORTHAND_REL[p1]:
            return True
    if p2 in SHORTHAND_REL:
        if p1 in SHORTHAND_REL[p2]:
            return True
    if p1 in SHORTHAND_REL and p2 in SHORTHAND_REL:
        if not set(SHORTHAND_REL[p1]).isdisjoint(SHORTHAND_REL[p2]):
            return True
    return False

def fromfile(filename, make_clique_css = False):
    """Constructs a simpleCSS object from a given CSS file

    :param filename:
        The name as a string of the CSS file
    :param make_clique_css:
        Whether to return a cliqueCSS as well as simpleCSS
    :returns:
        a simpleCSS object representing the file or a pair (simpleCSS, cliqueCSS)
    """
    css = cssfile.fromfile(filename)
    return fromcssfile(css, make_clique_css)

def fromstring(css, make_clique_css = False):
    """Constructs a simpleCSS object from a given CSS string

    :param css:
        The string representation of the CSS file
    :param make_clique_css:
        Whether to make a cliqueCSS
    :returns:
        if make_clique_css is false (default):
            a simpleCSS object representing the file
        else:
            a pair (simpleCSS, cliqueCSS)
            where
                simpleCSS is a simpleCSS object representing the file
                cliqueCSS is the file as a cliqueCSS object
    """
    css = cssfile.fromstring(css)
    return fromcssfile(css, make_clique_css)

def fromcssfile(css, make_clique_css = False):
    """Constructs a simpleCSS object from a given CSSFile

    :param css:
        The CSSFile
    :param make_clique_css:
        Whether to make a cliqueCSS
    :returns:
        if make_clique_css is false (default):
            a simpleCSS object representing the file
        else:
            a pair (simpleCSS, cliqueCSS)
            where
                simpleCSS is a simpleCSS object representing the file
                cliqueCSS is the file as a cliqueCSS object
    """
    # dict from (prop, selector, value) to simpleRule
    rules = {}
    prop_names = dict()

    for p in css.get_props():
        for spec in css.get_specificities(p):
            for (s, v) in css.get_values(p, spec):
                (l, unique) = css.get_info(p, spec, s, v)
                rules[(p, s, v)] = _make_simple_rule(p,
                                                     cssfile.selector_str(s),
                                                     v,
                                                     unique)
                prop_names[_make_prop(p, v)] = p

    reset_selectors_overlap_memo()
    order = set()

    for p in css.get_props():
        for spec in css.get_specificities(p):
            for ((p1, s1, v1), (p2, s2, v2)) in _iter_related_comb(p, spec, css):
                # p1 != p2 if e.g. p = p2 is font and p1 is font-weight
                if p1 != p2 or v1 != v2:
                    e1 = rules[(p1, s1, v1)]
                    e2 = rules[(p2, s2, v2)]

                    # first check that a potential edge order wouldn't
                    # be mitigated by a later rule.  I.e.,
                    #    (s1,p1,v1) < (s2,p1,v2)
                    # would be pointless if (s2,p1,v1) appears later in
                    # the file -- if v1 is not a valid value, s2 would
                    # fall back to v2 regardless of s1's value (v1 would
                    # also fail there).  If v1 is valid, then s2 would
                    # already assign it and v2 would be ignored, so we
                    # can safely put (s1,p1,v1) after (s2,p1,v2)

                    (l1, _) = css.get_info(p1, spec, s1, v1)
                    (l2, _) = css.get_info(p2, spec, s2, v2)

                    if full_selectors_overlap(s1, s2):
                        if l2 < l1:
                            killer_info = css.get_info(p2, spec, s1, v2)
                            killed = False
                            if killer_info is not None:
                                (l3, _) = killer_info
                                killed = l3 > l1
                            if not killed:
                                order.add((e2, e1))
                        else:
                            killer_info = css.get_info(p1, spec, s2, v1)
                            killed = False
                            if killer_info is not None:
                                (l3, _) = killer_info
                                killed = l3 > l2
                            if not killed:
                                order.add((e1, e2))

    complex_rules = [ _make_rule(r) for r in css.get_rules() ]
    simple_css = simpleCSS(list(rules.values()),
                           list(order),
                           complex_rules,
                           prop_names = prop_names)

    clique_css = None
    if make_clique_css:
        rule_pairs = [ _make_rule_pair(r) for r in css.get_rules() ]
        clique_css = cliqueCSS(rule_pairs, prop_names)

    if not make_clique_css:
        return simple_css
    else:
        return (simple_css, clique_css)

def cliquefromfile(filename):
    """Constructs a cliqueCSS object from a given CSS file

    :param filename:
        The name as a string of the CSS file
    :returns:
        a cliqueCSS object representing the file
    """
    css = cssfile.fromfile(filename)
    return cliquefromcssfile(css)

def cliquefromstring(css):
    """Constructs a cliqueCSS object from a given CSS string

    :param css:
        The string representation of the CSS file
    :returns:
        a cliqueCSS object representing the file
    """
    css = cssfile.fromstring(css)
    return cliquefromcssfile(css, make_clique_css)

def cliquefromcssfile(css, make_clique_css = False):
    """Constructs a cliqueCSS object from a given CSSFile

    :param css:
        The CSSFile
    :returns:
        a cliqueCSS object representing the file
    """
    # dict from (prop, selector, value) to simpleRule
    prop_names = dict()

    for p in css.get_props():
        for spec in css.get_specificities(p):
            for (_, v) in css.get_values(p, spec):
                prop_names[_make_prop(p, v)] = p

    rule_pairs = [ _make_rule_pair(r) for r in css.get_rules() ]

    return cliqueCSS(rule_pairs, prop_names)


def _make_rule(r):
    """
    :param r:
        CSSRule
    :returns:
        a rule object from simpleCSS built from the given CSSRule
    """
    (ss, pp) = _make_rule_pair(r)
    return rule(ss, pp)

def _make_rule_pair(r):
    """
    :param r:
        CSSRule
    :returns:
        a pair (ss, pp) representing the rule, where ss is a set of selectors in
        the same format as simpleRule selectors and ps is a set of properties in
        the same format as simpleRule
    """
    decls = [ _make_prop(p, v) for (p, v) in r.get_declarations() ]
    sels = { cssfile.selector_str(s) for s in r.get_selectors() }
    return (sels, decls)

def _make_simple_rule(prop, sel, value, unique = True):
    """
    :param prop:
        The property in same format as simpleRule
    :param sel:
        The selector in same format as simpleRule
    :param value:
        The value as a string
    :param unique:
        The simpleCSS rule only appears once in the file
    :returns:
        A simpleRule made from the arguments
    """
    return simpleRule(sel,
                      _make_prop(prop, value))

def _make_prop(prop, value):
    return prop + ":" + value

_selectors_overlap_memo = dict()
_selectors_automata = dict()

def reset_selectors_overlap_memo():
    """
    _selectors_overlap and _make_selector_automata are memoized to speed it up.
    Call this to reset.
    """
    global _selectors_overlap_memo
    global _selectors_automata
    _selectors_overlap_memo = dict()
    _selectors_automata = dict()

def selectors_overlap_str(css1, css2):
    """
    Note: is memoized, call reset_selectors_overlap_memo before using.

    :param css1:
        css selector as string
    :param css2:
        css selector as string
    :returns:
        True iff the two selectors may match the same node
    """
    s1 = cssselect_parser.parse(css1).pop()
    s2 = cssselect_parser.parse(css2).pop()

    return full_selectors_overlap(s1, s2)

def full_selectors_overlap(css1, css2):
    """
    Note: is memoized, call reset_selectors_overlap_memo before using.

    :param css1:
        css selector as cssselect Selector
    :param css2:
        css selector as cssselect Selector
    :returns:
        True iff the two selectors may match the same node
    """
    if css1.pseudo_element != css2.pseudo_element:
        return False

    pt1 = css1.parsed_tree
    pt2 = css2.parsed_tree
    return selectors_overlap(pt1, pt2)


def selectors_overlap(css1, css2):
    """
    Note: is memoized, call reset_selectors_overlap_memo before using.

    :param css1:
        css selector as cssselect parsed tree
    :param css2:
        css selector as cssselect parsed tree
    :returns:
        True iff the two selectors may match the same node
    """
    global numchecks
    global numpositive
    global numnontrivialchecks
    global numpositivenontrivial

    if _selectors_overlap_memo.has_key((css1, css2)):
        return _selectors_overlap_memo[(css1, css2)]
    elif _selectors_overlap_memo.has_key((css2, css1)):
        return _selectors_overlap_memo[(css2, css1)]
    else:
        numchecks += 1
        fast_res = _shortcut_selectors_overlap(css1, css2)
        if fast_res is not None:
            if fast_res:
                numpositive += 1
            return fast_res
        numnontrivialchecks += 1
        aut1 = _make_selector_automata(css1)
        aut2 = _make_selector_automata(css2)
        aut = cssautomaton.intersect(aut1, aut2)
        result = not autemptiness.isempty(aut, (cssfile.selector_str_pt(css1), cssfile.selector_str_pt(css2)))
        _selectors_overlap_memo[(css1, css2)] = result
        if result:
            numpositive += 1
            numpositivenontrivial += 1
        return result

def _shortcut_selectors_overlap(css1, css2):
    """Implements some fast checks for selector overlap
    :param css1:
        css selector as cssselect parsed_tree
    :param css2:
        css selector as cssselect parsed_tree
    :returns:
        True/False if a quick diagnosis of overlap between selectors could be made
        else None
    """

    def is_star(css):
        """
        :param css:
            css selector as parsed tree
        :returns:
            True iff css is .c for some c
        """
        return (type(css).__name__ == "Element" and
                css.namespace == None and
                css.element == None)

    def is_class(css):
        """
        :param css:
            css selector as parsed tree
        :returns:
            True iff css is .c for some c
        """
        return (type(css).__name__ == "Class" and
                is_star(css.selector))

    def is_hash(css):
        """
        :param css:
            css selector as parsed tree
        :returns:
            True iff css is #i for some i
        """
        return (type(css).__name__== "Hash" and
                is_star(css.selector))

    def is_element(css):
        """
        :param css:
            css selector as parsed tree
        :returns:
            True iff css is n|e for some n|e
        """
        return type(css).__name__== "Element"

    def all_classes_pseudo(css):
        """
        :param css:
            css selector as parsed tree
        :returns:
            True iff css is a complex selector built only from .c atoms
            e.g. .c > .d
            p as string if css is complex selector built only from .c atoms but
            ending with :p
        """
        if is_star(css):
            return True
        elif (type(css).__name__ == "Class" and
              all_classes_pseudo(css.selector) is not False):
            return True
        elif (type(css).__name__ == "CombinedSelector" and
              all_classes_pseudo(css.selector) is not False and
              all_classes_pseudo(css.subselector) is not False):
            return True
        elif (type(css).__name__ == "Pseudo" and
              all_classes_pseudo(css.selector) is not False):
            return css.ident
        else:
            return False

    if is_class(css1) and is_class(css2):
        return True
    elif is_hash(css1) and is_hash(css2):
        return css1.id == css2.id
    elif is_element(css1) and is_element(css2):
        return css1 == css2

    p1 = all_classes_pseudo(css1)
    p2 = all_classes_pseudo(css2)
    if not(p1 is False or p2 is False):
        if p1 is True or p2 is True:
            return True
        elif ((p1, p2) in autemptiness.get_local_conflict_ps() or
              (p2, p1) in autemptiness.get_local_conflict_ps()):
            return False

    return None

def _make_selector_automata(css):
    """
    Note: is memoized, call reset_selectors_overlap_memo before using

    :param css:
        A css selector in parsed_tree cssselect format
    :returns:
        An automaton representation of the selector
    """
    if _selectors_automata.has_key(css):
        return _selectors_automata[css]
    else:
        aut = cssautomaton.fromselector(css)
        _selectors_automata[css] = aut
        return aut

def _iter_related_comb(p, spec, css):
    """
    :param p:
        Property name (string)
    :param spec:
        Specificity (!important, (a, b, c))
    :param css:
        The CSSFile
    :returns:
        Iterable over all combinations (not permutations) ((p1, s1, v1), (p2, s2, v2))
        representing declarations in file with same specificity where
            p' is either p or a contained within p (if p shorthand)
            p and p' are shorthands that set the same property
            s is selector
            v is value assigned
    """
    selvals = css.get_values(p, spec)
    for (s1, v1), (s2, v2) in combinations(selvals, 2):
        yield (p, s1, v1), (p, s2, v2)

    if p in SHORTHAND_REL:
        subps = set(SHORTHAND_REL[p])
        # the direct subs
        for subp in subps:
            for (subs, subv) in css.get_values(subp, spec):
                for (s, v) in selvals:
                    yield (p, s, v), (subp, subs, subv)
        # those that may set same property
        for altp in SHORTHAND_REL:
            if p != altp and not subps.isdisjoint(SHORTHAND_REL[altp]):
                for (alts, altv) in css.get_values(altp, spec):
                    for (s, v) in selvals:
                        yield (p, s, v), (altp, alts, altv)

