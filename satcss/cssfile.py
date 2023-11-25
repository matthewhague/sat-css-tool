
"""Module for opening a CSS file and extracting the required SAT information."""

from collections import defaultdict
from itertools import islice
from math import ceil

import tinycss2
import satcss.cssselect_parser as cssselect_parser

# Let's assume this will never appear in any CSS file...
multiprop_separator = "#+#"


_BAD_ATTR_CHARS = set(" \t\n\r\f\"'`=<>#/")
_ID_ESCAPE_CHARS = "\\!\"#$%&'()*+,./:;<=>?@[]^`{|}~"

class CSSFileException(Exception):
    pass

# FakeValue and FakeDeclaration used in __build_data_structures to streamline
# code

class FakeValue:
    def __init__(self, v):
        self.__value = v

    def as_css(self):
        return self.__value

class FakeDeclaration:
    def __init__(self, name, priority, value):
        self.name = name
        self.lower_name = name.lower()
        self.priority = priority
        self.value = FakeValue(value)

def fromfile(filename, multiprop = False):
    """Function for parsing the CSS file

    :param filename:
        string name of file to parse
    :param multiprops:
        Argument as in CSSFile, default False
    :returns:
        a CSSFile representation of the CSS file
    """
    bytes = open(filename).read()
    stylesheet = tinycss2.parse_stylesheet(bytes,
                                           skip_whitespace=True,
                                           skip_comments=True)
    return CSSFile(stylesheet, multiprop)

def fromstring(css, multiprop = False):
    """Function for parsing the CSS

    :param css:
        string containing some CSS
    :param multiprop:
        As in CSSFile, default False
    :returns:
        a CSSFile representation of the CSS
    """
    stylesheet = tinycss2.parse_stylesheet(css,
                                           skip_whitespace=True,
                                           skip_comments=True)
    return CSSFile(stylesheet)

def selector_str(sel):
    """
    :param sel:
        A cssselect Selector
    :returns:
        Selector as a string
    """
    if sel.pseudo_element:
        return selector_str_pt(sel.parsed_tree) + '::' + sel.pseudo_element
    else:
        return selector_str_pt(sel.parsed_tree)

def selector_str_pt(tree, needstar = True):
    """Turns a cssselect selector tree into a string -- main just a function
    for practicing navigating the cssselect AST

    :param tree:
        The cssselect selector tree to turn to a string
    :param needstar:
        True iff universal selectors need to be represented with * rather than blank
    :returns:
        A string representation of selector
    """
    def spaced_combinator(comb):
        if comb == ' ':
            return ' '
        else:
            return comb

    star = "*" if needstar else ""

    def esc_id(ident):
        """For escaping class names, attribute names, and so on"""
        # can't find a better way
        if '\\' in _ID_ESCAPE_CHARS:
            ident = ident.replace('\\', '\\\\')
        for c in _ID_ESCAPE_CHARS:
            if c != '\\':
                ident = ident.replace(c, '\\' + c)
        return ident

    def format_attribute_sel(tree):

        def needs_quote(value_str):
            if value_str is None:
                return False

            # rules according to
            # https://mothereff.in/unquoted-attributes#nofollow

            if len(value_str) == 0:
                return True

            if value_str == "-":
                return True

            # hash included because cssselect_parser does not like it
            if bool(set(value_str) & _BAD_ATTR_CHARS):
                return True

            if value_str[0].isdigit():
                return True

            if len(value_str) < 2:
                return False
            else:
                if value_str[0:2] == "--":
                    return True
                if value_str[0] == "-" and value_str[1].isdigit():
                    return True

                return False

        value_str = tree.value
        if needs_quote(value_str):
            value_str = '"' + value_str + '"'
        parent_str = (selector_str_pt(tree.selector, False)
                      if tree.selector is not None
                      else "")
        namespace_str = ("*|"
                         if tree.namespace is None
                         else (""
                               if tree.namespace == ""
                               else esc_id(tree.namespace) + "|"))
        opval_str = (tree.operator + _str_unicode(value_str)
                     if tree.operator != "exists"
                     else "")
        return (parent_str +
                "[" + namespace_str + tree.attrib + opval_str + "]")

    # matching on typename like this seems like a terrible hack, but it's
    # how cssselect implements its own traversal...
    stype = type(tree).__name__
    return {
    "Attrib" : lambda : format_attribute_sel(tree),
    "CombinedSelector" : lambda :
        selector_str_pt(tree.selector, True) +
        spaced_combinator(tree.combinator) +
        selector_str_pt(tree.subselector, True),
    "Class" : lambda :
        (selector_str_pt(tree.selector, False) if tree.selector is not None else "") +
        "." + esc_id(tree.class_name),
    "Element" : lambda :
        (esc_id(tree.namespace) + "|" if tree.namespace is not None else "") +
        (tree.element if tree.element is not None else star),
    "Function" : lambda :
        (selector_str_pt(tree.selector, False) if tree.selector is not None else "") +
        ":" + tree.name +
        # There are only a finite number of token string patters: an + b, an, b
        "(" + ''.join(map(_token_str, tree.arguments)) + ')',
    "Hash" : lambda :
        (selector_str_pt(tree.selector, False) if tree.selector is not None else "") +
        "#" + esc_id(tree.id),
    "Negation" : lambda :
        (selector_str_pt(tree.selector, False) if tree.selector is not None else "") +
        ":not(" +
        selector_str_pt(tree.subselector, True) +
        ")",
    "Pseudo" : lambda :
        (selector_str_pt(tree.selector, False) if tree.selector is not None else "") +
        ":" + tree.ident
    }[stype]()

def get_fun_sel_coefs(sel):
    """Extracts a and b from :nth-*(an + b) selectors.

    :param sel:
        The selector as a Function from cssselect
    :returns:
        Two integers (a, b) that are the coefficients in the selector
    """
    def raise_error():
        raise CSSFileException("Cannot get a and b from " + str(sel))
    # Cases:
    #   1 argument: f(b) or f(n)
    #   2 arguments: f(an) or (nopb) (e.g. (n+4) is 'n' '+4')
    #   3 arguments: f(n op b) or f(anopb) (e.g. (3n+4) is '3' 'n' '+4')
    #   4 arguments: f(an op b) (even if a negative)
    l = len(sel.arguments)
    if l == 1:
        tb = sel.arguments[0]
        if tb.type == "NUMBER":
            return (0, int(tb.value))
        elif (tb.type == "IDENT" and
              tb.value == "n"):
            return (1, 0)
        elif (tb.type == "IDENT" and
              tb.value == "even"):
            return (2, 0)
        elif (tb.type == "IDENT" and
              tb.value == "odd"):
            return (2, 1)
        else:
            print("Tb type: ", tb.type)
            raise_error()
    elif l == 2:
        t1, t2 = sel.arguments
        if (t1.type == "NUMBER" and
            t2.type == "IDENT" and
            t2.value == "n"):
            return (int(t1.value), 0)
        elif (t1.type == "IDENT" and
              t1.value == "n" and
              t2.type == "NUMBER"):
            return (1, int(t2.value))
        elif (t1.type == "IDENT" and
              t1.value == "-n" and
              t2.type == "NUMBER"):
            return (-1, int(t2.value))
        # Case below because of weird parsing bug where "2n-1" is
        # lexed to "2" "n-1"
        elif (t1.type == "NUMBER" and
              t2.type == "IDENT" and
              t2.value.startswith("n-")):
            return (int(t1.value), -int(t2.value[2:]))
        elif (t1.type == "NUMBER" and
              t2.type == "IDENT" and
              t2.value.startswith("n+")):
            return (int(t1.value), int(t2.value[2:]))
        else:
            print("T1:", t1.type)
            print("T2:", t2.type)
            raise_error()
    elif l == 3:
        t1, t2, t3 = sel.arguments
        if (t1.type == "IDENT" and
            t1.value == "n" and
            t2.type == "DELIM" and
            t2.value in ["+", "="] and
            t3.type == "NUMBER"):
            return (1, int(t2.value + t3.value))
        elif (t1.type == "NUMBER" and
              t2.type == "IDENT" and
              t2.value == "n" and
              t3.type == "NUMBER"):
            return (int(t1.value), int(t3.value))
        else:
            raise_error()
    elif l == 4:
        ta, tn, top, tb = sel.arguments
        if (ta.type == "NUMBER" and
            tn.type == "IDENT" and
            tn.value == "n" and
            top.type == "DELIM" and
            top.value in ["+", "-"] and
            tb.type == "NUMBER"):
            return (int(ta.value),
                    int(top.value + tb.value))
    else:
        raise_error()

class CSSRule:
    """Representation of a CSS rule"""

    def __init__(self, selectors, declarations):
        self.__selectors = frozenset(selectors)
        self.__declarations = declarations

    def get_selectors(self):
        """:returns: set of cssselect parsed_tree selectors"""
        return self.__selectors

    def get_declarations(self):
        """:returns: set of pairs (p, v) for as strings for propert and value"""
        return self.__declarations

    def __str__(self):
        return (",".join([selector_str(s) for s in self.__selectors]) +
                "{" +
                ";".join([str(p) + ": " + str(v)
                          for (p, v) in self.__declarations]) +
                "}")

    def __eq__(self, other):
        return (other.__class__.__name__ == self.__class__.__name__ and
                set(self.__selectors) == set(other.__selectors) and
                set(self.__declarations) == set(other.__declarations))

    def __hash__(self):
        return hash(self.__selectors) + hash(self.__declarations)


class CSSFile:
    """Representation of a CSS file and methods for extracting required
    information.  Designed to be navigated using get_props() then
    get_specificities(prop), then get_values(prop, spec) which returns a list of
    tuples (selector, value) and can use get_info(prop, spec, selector, value)
    """

    def __init__(self,
                 stylesheet,
                 multiprop = False,
                 first_rule_idx = None,
                 last_rule_idx = None):
        """Create a CSSFile object

        :param stylesheet:
            A stylesheet parsed by tinycss2
        :param multiprops:
            Combines multiply defined properties in one rule into a single declaration with multiple values
            E.g. { p: a; p: b } becomes a single { p : a+b } rather than two declarations
            where + is actually cssfile.multiprop_separator
        :param first_rule_idx:
            Construct from a contiguous subset of the stylesheet, that is, from the first_rule_idx (inclusive)...
        :param last_rule_idx:
            ...to the last_rule_idx (exclusive).  Both None if the whole style sheet is to be used
        :raises:
            IOError if file cannot be read
        """
        self.stylesheet = stylesheet
        self.ignored_rules = [] # populated by self.__build_data_structures
        if first_rule_idx is None:
            self.first_rule_idx = 0
            self.last_rule_idx = len(stylesheet)
        else:
            self.first_rule_idx = first_rule_idx
            self.last_rule_idx = last_rule_idx
        (self.props, self.rules) = self.__build_data_structures(multiprop)
        self.multiprop = multiprop

    def is_multiprop():
        """
        :returns: True if file built with multiprop argument
        """
        return self.multiprop

    def get_props(self):
        """
        :returns:
            The list of CSS properties (such as font-style) defined in the
            CSS file as a iteration over strings
        """
        return list(self.props.keys())

    def get_specificities(self, prop):
        """
        :param prop:
            A string property name
        :returns:
            An iteration over a list of selector specificities that define the
            given property name, as tuples (!important (bool), (a, b, c) (ints))
        """
        return list(self.props[prop].keys())

    def get_values(self, prop, spec):
        """
        :param prop:
            A string property name
        :param spec:
            A tuple (!important (bool), (a, b, c) (ints)) giving specificity
        :returns:
            Set of tuples (sel (cssselect parsed_tree),
                           val (string (includes !important)))
            meaning prop is assigned val under selector sel with given specificity
            info.
        """
        return list(self.props[prop][spec].keys())

    def get_info(self, prop, spec, sel, val):
        """
        :param prop:
            A string property name
        :param spec:
            A tuple (!important (bool), (a, b, c) (ints)) giving specificity
        :param sel:
            A cssselect parsed_tree selector for a sel { val } pair
        :param val:
            The value to go with the selector
        :returns:
            (line_no, unique)
            line_no -- The line number where sel { val } last appears
                       (indicative, not precise)
            unique -- boolean True iff sel { prop: val } only appears once in the file

            or None if it isn't contained
        """
        try:
            return self.props[prop][spec][(sel, val)]
        except KeyError:
            return None

    def num_rules(self):
        """:returns: The number of rules in the CSS file."""
        return len(self.rules)

    def num_properties(self):
        """:returns: the number of distinct property tags (e.g. width,
        font-face) in the file"""
        return len(self.props)

    def get_rules(self):
        """:returns: set of CSSRules"""
        return self.rules

    def get_ignored_rules(self):
        """:returns: a list of strings of rules that are not supported, e.g. @font-face"""
        return self.ignored_rules

    def split_css(self, size):
        """
        :param size:
            The maximum number of rules to appear in a chunk
        :returns:
            A list of CSSFile objects, each containing a contiguous chunk of self
        """
        num_chunks = int(ceil(len(self.stylesheet) / float(size)))
        return [ CSSFile(self.stylesheet,
                         self.multiprop,
                         size * i,
                         size * (i+1))
                 for i in range(num_chunks) ]



    def __str__(self):
        s = []
        for rule in self.stylesheet:
            s.append(tinycss2.serialize(rule))
        return ''.join(s)

    def __parse_selector(self, selector):
        """Function for parsing a selector from a tinycss token
        representation to a cssselect object representation

        :param selector:
            The selector as a component value list from tinycss
        :returns:
            A list of Selector objects from cssselect
            representing the selector (which may have had ,s)
        """
        return cssselect_parser.parse(tinycss2.serialize(selector))

    def __selector_str(self, selector):
        """Turns a cssselect selector into a string -- main just a function
        for practicing navigating the cssselect AST

        :param selector:
            The cssselect Selector to turn to a string
        :returns:
            A string representation of selector
        """
        return selector_str(selector)

    def __build_data_structures(self, multiprop):
        """Call after stylesheet has been parsed

        :param multiprop:
            As in __init__
        :returns:
            (props, rules)

            props is dict from
                prop_name (string) ->
                    (!important (bool), specificity (a, b, c)) ->
                        dict from
                            (selector (parsed_tree),
                             value (normalised string with !important)) ->
                                pair of:
                                line_no (int, not precise line_no but keeps order,
                                         and is last occurrence of sel, v in file)
                                boolean -- True if rule appears only once in file

            rules is set of pairs (S, P) where S is set of cssselect Selector
            and props is a list of pairs (p, v) of strings property and value
        """

        def get_decl_value(decl):
            """Returns decl.value normalised and with !important
            appended if needed"""
            val = tinycss2.serialize(decl.value)
            normed = self.__normalise_css_value(val)
            important = "!important" if decl.important else ""
            return normed + important


        props = defaultdict(lambda : defaultdict(dict))
        rules = list()
        line_no = 1
        for rule in islice(self.stylesheet,
                           self.first_rule_idx,
                           self.last_rule_idx):
            sels = set()
            declarations = None

            if rule.type != "qualified-rule":
                rule_str = tinycss2.serialize([rule])
                self.ignored_rules.append(rule_str)
                print("WARNING: merely copying rule ", rule_str)
                continue

            parsed_rule_decls = tinycss2.parse_declaration_list(rule.content,
                                                                skip_whitespace=True,
                                                                skip_comments=True)
            rule_declarations = []

            for i, decl in enumerate(parsed_rule_decls):
                if decl.type == "error":
                    print("WARNING: parser error in", i+1, "th declaration of")
                    print(tinycss2.serialize(rule.content))
                    print(decl.message)
                    print("Ignoring declaration")
                    continue
                rule_declarations.append(decl)

            if not multiprop:
                declarations = rule_declarations
            else:
                declarations = []

                # keep !important and not important separate, to be on the safe
                # side
                combined = defaultdict(list)
                for decl in rule_declarations:
                    val = self.__normalise_css_value(tinycss2.serialize(decl.value))
                    combined[(decl.lower_name, decl.important)].append(val)

                def build_val(vals):
                    return multiprop_separator.join(vals)

                for ((name, priority), vals) in combined.items():
                    decl = FakeDeclaration(name, priority, build_val(vals))
                    declarations.append(decl)

            decls = [ (decl.lower_name, get_decl_value(decl))
                      for decl in rule_declarations ]

            # reset line number to beginning of rule after each selector
            line_no_start = line_no
            for sel in self.__parse_selector(rule.prelude):
                sels.add(sel)
                line_no = line_no_start
                for decl in declarations:
                    v = get_decl_value(decl)
                    specificity = (decl.important,
                                   sel.parsed_tree.specificity())
                    tup = (sel, v)
                    m = props[decl.lower_name][specificity]
                    m[tup] = (line_no, not tup in m)
                    line_no += 1

            rules.append(CSSRule(sels, decls))

        return (props, rules)

    def __normalise_css_value(self, value):
        """At the moment this does nothing but remove unicode, but should really
        do things like remove spaces, convert all colours to hex format and so
        on.

        :param value:
            String giving a value of a css property
        :returns:
            A normalisation of that value
        """
        return _str_unicode(value).strip()



def _token_str(token):
    """Turns a cssselect token into a string -- used for arguments to
    function selectors

    :param token:
        The token to translate to a string
    :returns:
        A string representation of the token
    """
    ttype = token.type
    return {
    "NUMBER" : lambda :
        token.value,
    "IDENT" : lambda :
        token.value,
    "DELIM" : lambda :
        token.value,
    }[ttype]()

def _str_unicode(o):
    """Act as a str(...) function for something that might
    be unicode, but might not...

    :param:
        o the object to encode as a string or None
    """
    if o is None:
        return str(o)
    else:
        return o.encode("utf-8").decode()
