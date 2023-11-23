"""A representation of CSS files as cliques of selectors and properties"""

from itertools import product
from collections import defaultdict

from cssfile import selector_str
import simpleCSS as Sim

__DEBUG__ = True

# This variable is used below in the sort_decls
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
                  "border": ["border-width",
                             "border-top",
                             "border-bottom",
                             "border-left",
                             "border-right",
                             "border-width",
                             "border-color",
                             "border-style",
                             "border-top-width",
                             "border-right-width",
                             "border-bottom-width",
                             "border-left-width",
                             "border-top-style",
                             "border-right-style",
                             "border-bottom-style",
                             "border-left-style",
                             "border-top-color",
                             "border-right-color",
                             "border-bottom-color",
                             "border-left-color"],
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

class cliqueCSS:

    def __init__(self, cliques = None, prop_names = dict(), ignored_rules = []):
        """
        :param cliques:
            A list of pairs (ss, ps) where ss is a set of selectors in the same format as simpleRule
            selectors and ps is a list of properties in the same format as simpleRule
        :param prop_names:
            a map from properties (of the form "p: v" to the name of the
            property defined (p)
        :param ignored_rules:
            A list of string representations of rules that are note sel
            { decl } rules.  E.g. @font-face.  These will be output with
            string representations, but otherwise not handled.
        """
        if cliques == None:
            self.cliques = []
        else:
            self.cliques = list(cliques)

        self.prop_names = prop_names
        self.ignored_rules = ignored_rules

    def remove_rule(self, i):
        """
        Removes rule at given index

        :param i:
            An index in range of number of rules in cliqueCSS
        """
        self.cliques.pop(i)

    def add_rule(self, selectors, properties):
        """Adds the rule selectors { properties } to the CSS

        :param selectors:
            A set of selectors in same format as simpleRule
        :param properties:
            A list of properties represented same as in simpleRule, where the
            ordering reflects the order they should appear in the file
        """
        self.cliques.append((selectors, properties))

    def insert_rule(self, i, selectors, properties):
        """
        Insert a new rule between the rule at index i-1 and i (same as python
        list insert)

        :param selectors:
            A set of selectors in same format as simpleRule
        :param properties:
            A list of properties represented as in simpleRule, where the
            ordering reflects the order they should appear in the file
        :param i:
            Insert the new rule between rule at index i and index i+1
        """
        self.cliques.insert(i, (selectors, properties))

    def num_rules(self):
        return len(self.cliques)

    def num_nodes(self):
        """:return: the number of nodes in the CSS.  A node is either a selector
        or property appearing in a rule"""
        count = 0
        for (ss, pp) in self.cliques:
            count += len(ss)
            count += len(pp)
        return count

    def size(self):
        """:return: the number of bytes needed for the properties and selectors"""
        return sum([self.clique_size(c) for c in self.cliques])

    def clique_size(self, xxx_todo_changeme):
        """
        :param (ss, pp):
            A biclique where ss in a set of selectors and pp a list of
            properties
        :returns:
            The size of the clique in bytes with two braces, commas between sels
            and ; between props
        """
        (ss, pp) = xxx_todo_changeme
        return (sum([len(s) for s in ss]) +
                sum([len(p) for p in pp]) +
                len(ss) + len(pp))


    def build_last_index_map(self):
        """Note: constructs map anew each call.

        :returns:
            A map where last_index[simpleRule(s, p)] returns the index of the last
            bucket containing that edge
        """
        last_index = dict()
        for (i, (ss, pp)) in enumerate(self):
            for (s, p) in product(ss, pp):
                simple = Sim.simpleRule(s,p)
                last_index[simple] = i
        return last_index

    def build_rev_last_index_map(self):
        """Note: constructs map anew each call.

        :returns:
            A map where last_index[i] returns the set of edges that last appear at index i
        """
        rev_last_index = defaultdict(set)

        for (e, i) in self.build_last_index_map().items():
            rev_last_index[i].add(e)

        return rev_last_index


    def build_first_index_map(self):
        """Note: constructs map anew each call.

        :returns:
            A map where first_index[simpleRule(s, p)] returns the index of the first
            bucket containing that edge
        """
        first_index = dict()
        for (i, (ss, pp)) in enumerate(self):
            for (s, p) in product(ss, pp):
                simple = Sim.simpleRule(s,p)
                if simple not in first_index:
                    first_index[simple] = i
        return first_index


    def last_index_of(self, r, i = 0):
        """
        :param r:
            A simpleRule
        :param i:
            An index in range(self.num_rules())
        :returns:
            -1 if r does not appear in the CSS file in rule i or later
            the largest j >= i where r appears in rule j of the file
        :throws:
            IndexError if i out of range
        """
        if i < 0 or i >= len(self.cliques):
            raise IndexError

        s = r.getSelector()
        p = r.getProperty()

        for j in range(len(self.cliques) - 1, i - 1, -1):
            (ss, pp) = self.cliques[j]
            if s in ss and p in pp:
                return j

        return -1

    def first_index_of(self, rSet, i = 0):
        """
        :param rSet:
            A set of simpleRule
        :param i:
            An index in range(self.num_rules())
        :returns:
            -1 if r does not appear in the CSS file in rule i or later
            the smallest j >= i where r appears in rule j of the file
        :throws:
            IndexError if i out of range
        """
        if i < 0 or i >= len(self.cliques):
            raise IndexError


        for j in range(i,len(self.cliques)):
            (ss, pp) = self.cliques[j]
            for r in rSet:
                s = r.getSelector()
                p = r.getProperty()
                if s in ss and p in pp:
                    return j

        return -1

    #def add_simple_rule(self, r, i=0):
    def add_simple_rule(self, r1, r2, colored_edges):
        """
        :param r1:
            A simpleRule
        :param r2:
            A simpleRule
        :param colored_edges:
            edges (as pairs) appearing in edgeOrder from original CSS
        :returns:
            None. It assumes that r1 does not appear already in cliques.
            It assumes that r2 appears in cliques. It adds r to the first
            position where r2 appears and does not *add* edges in colored_edges
            when r1 is added.
        """

        s1 = r1.getSelector()
        p1 = r1.getProperty()
        s2 = r2.getSelector()
        p2 = r2.getProperty()

        for j in range(len(self.cliques)):
            (ss, pp) = self.cliques[j]
            # Case when both s1 and p1 already in cliques
            if s1 in ss and p1 in pp:
                good = True
                break
            if s2 in ss and p2 in pp:
                good = True
                for s3 in ss:
                    if p1 not in pp and (s3,p1) in colored_edges:
                        good = False
                        break
                if good:
                    for p3 in pp:
                        if s1 not in ss and (s1,p3) in colored_edges:
                            good = False
                            break
                if good:
                    ss.add(s1)
                    if not p1 in pp:
                        pp.append(p1)
                    break

        assert good, "Something wrong at the end of add_simple_rule"

    def add_rules(self, cliques):
        """Adds the given list of rules (cliques) to the end of the CSS
        :param cliques:
            A list of pairs (ss, ps) where ss is a set of selectors in the same format as simpleRule
            selectors and ps is a set of properties in the same format as simpleRule
        """
        self.cliques.extend(cliques)

    def concat(self, other):
        """ Add all buckets of other to the end of self
        :param other:
            A cliqueCSS object
        """
        self.add_rules(other.cliques)
        self.prop_names.update(other.prop_names)

    def get_edge_set(self, min_pos = 0, max_pos = -1):
        """Note: computes each time

        :param min_pos:
            For getting rules from a portion of the file, begin at min_pos.
            Must be in range(num_rules())
        :param max_pos:
            The last position to get edges from.
            Can be -1 to denote end of file
        :returns:
            a set of all simpleRules covered by the cliqueCSS
        """
        if max_pos < 0:
            max_pos = self.num_rules()

        return { Sim.simpleRule(s, p)
                 for i in range(min_pos, max_pos)
                 for (s, p) in product(self.cliques[i][0],
                                       self.cliques[i][1]) }

    def is_sub_css(self, css):
        """
        :param css:
            A simple CSS object
        :returns:
            True iff the object represents a CSS file that contains a subset of
            the edges of CSS and respects the order
        """
        edgeSet = self.get_edge_set()

        if not edgeSet <= css.edgeSet:
            if __DEBUG__:
                print('There are ' + str(len(edgeSet)) +' edges in edgeSet')
                print('There are ' + str(len(css.edgeSet)) +\
                        ' edges in css.edgeSet')
                print('There are ' + str(len(edgeSet - css.edgeSet)) +\
                        ' edges in edgeSet - css.edgeSet')
                print('There are ' + str(len(css.edgeSet - edgeSet)) +\
                        ' edges in css.edgeSet - edgeSet')
                print('Edges missing from simple css: ' +\
                        str(edgeSet - css.edgeSet))
            return False

        return self.__edge_order_respected(css.edgeOrder)

    def is_super_css(self, css):
        """
        :param css:
            A simple CSS object
        :returns:
            True iff the object represents a CSS file that contains a superset of
            the edges of CSS and respects the order
        """
        edgeSet = self.get_edge_set()

        if not css.edgeSet <= edgeSet:
            if __DEBUG__:
                print('There are ' + str(len(edgeSet)) +' edges in edgeSet')
                print('There are ' + str(len(css.edgeSet)) +\
                        ' edges in css.edgeSet')
                print('There are ' + str(len(edgeSet - css.edgeSet)) +\
                        ' edges in edgeSet - css.edgeSet')
                print('There are ' + str(len(css.edgeSet - edgeSet)) +\
                        ' edges in css.edgeSet - edgeSet')
                print('Edges missing from clique css: ' +\
                        str(css.edgeSet - edgeSet))
            return False

        return self.__edge_order_respected(css.edgeOrder)

    def sort_decls(self):
        """Sort the declarations in all cliques in the CSS"""

        #import simplecssbuilder
        #SHORTHAND_REL = simplecssbuilder.SHORTHAND_REL

        def decl_key(decl):
            """key for sorting declarations"""
            prop = decl.split(':')[0] # get property name
            if str(prop) in SHORTHAND_REL_inv:
                return SHORTHAND_REL_inv[str(prop)]
            else:
                return str(prop)

        def sort_decls_clique(clique):
            """Sort the declarations in clique"""
            (_,ps) = clique
            ps.sort(key=decl_key)

        # compute the inverse of SHORTHAND_REL
        SHORTHAND_REL_inv = dict()
        for k,vs in SHORTHAND_REL.items():
            for v in vs:
                SHORTHAND_REL_inv[v] = k

        #print 'PRINTING CLIQUES'
        for clique in self.cliques:
            #print clique
            sort_decls_clique(clique)
            #print clique


    def write_compact(self, fout):
        """Writes the represented CSS file in minimal form to fout.
        Includes ignored_rules.
        :param fout:
            Something with a .write() method, the file to write to
        """
        for ignored in self.ignored_rules:
            fout.write(ignored)
        self.sort_decls()
        for (pos, (ss, pp)) in enumerate(self.cliques):
            fout.write(','.join(sorted(ss)))
            fout.write('{')
            fout.write(';'.join(pp))
            fout.write('}')


    def get_orderable_max_bicliques(self, simple, max_split_factor = -1):
        """
        :param simple:
            A simpleCSS equivalent to the cliqueCSS
        :param max_split_factor:
            If > 0 then produce at most max_split_factor * num_max_bicliques new
            bicliques by splitting unorderable ones into orderable ones.  Once
            this limit is reached, simply stop generating any more.
            If 0 then throw away unorderable max bicliques
            If -1 then do not limit
        :returns:
            (bicliques_set, forbidden)
            where
                bicliques_set is a set of maximal and submaximal bicliques that is a
                set of the bicliques of simpleCSS.edgeList as a set of pairs (S,
                P) where S is a set of selectors from simpleRules and P is a set
                of properties from simpleRule.

                forbidden is a dict from positions in the clique to a set of
                bicliques from bicliques_set that are forbidden from position i
                onwards.

                bicliques_set will contain all sub maximal bicliques that are
                orderable at some point in the file.  A biclique is orderable at
                position i, if it is not in some forbidden[j] for all j <= i
        """
        max_bicliques = simple.get_max_bicliques()

        # All of the bicliques we generate, returned at end
        all_bicliques = set(max_bicliques)

        # dict from position to those forbidden at position
        forbidden = defaultdict(set)

        # those that become bad at some point in the file
        # (if it become bad, it is bad at end)
        bad_bicliques = { (ss, pp) for (ss, pp) in max_bicliques
                                   if not simple.is_orderable_biclique(ss, pp) }
        print("There are", len(bad_bicliques), "eventually bad bicliques out of", len(max_bicliques))
        print("Biclique/rule ratio: ", len(max_bicliques) / float(len(self.cliques)))
        print("Bad/good ratio: ", len(bad_bicliques) / float(len(max_bicliques)))

        num_rules = self.num_rules()

        rev_last_index = self.build_rev_last_index_map()
        ignore_rules = self.get_edge_set()


        if max_split_factor == 0:
            print("Max split factor is 0, simply ignoring bad bicliques")
            all_bicliques -= bad_bicliques
        else:
            max_split = -1
            if max_split_factor >= 0:
                max_split = int(max_split_factor * len(max_bicliques))
                print("Making at most", max_split, "new bicliques")
            else:
                print("Making any number of new bicliques")

            for pos in range(num_rules + 1):
                # can't ignore rules that have had their last index
                if pos > 0:
                    ignore_rules -= rev_last_index[pos - 1]

                next_bad_bicliques = set()

                for (ss, pp) in bad_bicliques:
                    if simple.is_orderable_biclique(ss, pp, ignore_rules):
                        next_bad_bicliques.add((ss, pp))
                    else: # becomes bad here
                        forbidden[pos].add((ss, pp))

                        for (ss1, pp1) in simple.get_orderable_sub_max_bicliques(ss, pp, ignore_rules, max_split):
                            max_split -= 1
                            all_bicliques.add((ss1, pp1))
                            # check if this new one might be forbidden later
                            if not simple.is_orderable_biclique(ss1, pp1):
                                next_bad_bicliques.add((ss1, pp1))

                bad_bicliques = next_bad_bicliques

            print("There were", len(max_bicliques), " max bicliques, eventually orderable", len(all_bicliques))

        from main import get_enumeration_output
        if get_enumeration_output():
            print("Enumeration of bicliques Mi:")
            for (i, bc) in enumerate(all_bicliques):
                print(" ", i, ":", str(bc))
            if len(forbidden) == 0:
                print("No bicliques were forbidden!")
            else:
                print("Forbidden F:")
                for (i, bcs) in forbidden.items():
                    print(" ", i, ":")
                    for bc in bcs:
                        print("   ", str(bc))

        return (all_bicliques, forbidden)




    def __edge_order_respected(self, edgeOrder):
        """
        :param edgeOrder:
            A list of pairs of simpleRules (e1, e2) giving order e1 < e2
        :returns:
            True iff the cliqueCSS object respects the edgeOrder
        """
        last_occurence = dict()
        i = 0
        for (ss, pp) in self.cliques:
            for p in pp:
                for s in ss:
                    e = Sim.simpleRule(s, p)
                    last_occurence[e] = i
                    i += 1

        for (e1, e2) in edgeOrder:
            if (e1 in last_occurence and
                e2 in last_occurence and
                not last_occurence[e1] < last_occurence[e2]):
                print("Edge ", e1, " last appears at property position", last_occurence[e1])
                print("Edge ", e2, " last appears at property position", last_occurence[e2])
                print("But the first should appear before the second!")
                return False

        return True


    def equivalent(self, css):
        """
        :param css:
            A simple CSS object
        :returns:
            True iff the object represents the same CSS file as css.
            That is, contains the same edges and respects the order.
        """
        edgeSet = { Sim.simpleRule(s, p)
                    for (ss, pp) in self.cliques
                    for (s, p) in product(ss, pp) }

        if edgeSet != css.edgeSet:
            if __DEBUG__:
                print('There are ' + str(len(edgeSet)) +' edges in edgeSet')
                print('There are ' + str(len(css.edgeSet)) +\
                        ' edges in css.edgeSet')
                print('There are ' + str(len(edgeSet - css.edgeSet)) +\
                        ' edges in edgeSet - css.edgeSet')
                print('There are ' + str(len(css.edgeSet - edgeSet)) +\
                        ' edges in css.edgeSet - edgeSet')
                print('Edges missing from clique: ' +\
                        str(css.edgeSet - edgeSet))
                print('Edges missing from simple css: ' +\
                        str(edgeSet - css.edgeSet))
            return False

        last_occurence = dict()
        i = 0
        lo_to_bucket = dict()
        j = 0
        for (ss, pp) in self.cliques:
            for p in pp:
                for s in ss:
                    e = Sim.simpleRule(s, p)
                    last_occurence[e] = i
                    lo_to_bucket[i] = j
                    i += 1
            j += 1

        for (e1, e2) in css.edgeOrder:
            # TODO: fix so edges can be in same bucket as long as they can be
            # ordered
            if not last_occurence[e1] < last_occurence[e2]:
                print("Edge ", e1, " last appears at property position", last_occurence[e1])
                print("Edge ", e1, " last appears at bucket", \
                lo_to_bucket[last_occurence[e1]])
                print(self.cliques[lo_to_bucket[last_occurence[e1]]])
                print("Edge ", e2, " last appears at property position", last_occurence[e2])
                print("Edge ", e2, " last appears at bucket", \
                lo_to_bucket[last_occurence[e2]])
                print(self.cliques[lo_to_bucket[last_occurence[e2]]])
                print("But the first should appear before the second!")
                return False

        return True

    def equivalent_masked(self, css):
        """
        :param css:
            A simple CSS object
        :returns:
            True iff the object represents the same CSS file as css if property masking is taken into account.
            E.g. s {p: 1; p: 2} has p: 1 masked so not counted.
            Requires prop_names to have been given.
        """

        edgeSet = set()
        pnEdgeSet = set()

        for (ss, pp) in reversed(self.cliques):
            for s in ss:
                for p in reversed(pp):
                    pn = self.prop_names[p]
                    if (s, pn) not in pnEdgeSet:
                        pnEdgeSet.add((s, pn))
                        edgeSet.add(Sim.simpleRule(s, p))

        simple_trcl = css.getTrClEdgeOrder()
        simple_masked = { r1
                          for (r1, r2) in css.getTrClEdgeOrder()
                          if ((r1.getSelector() == r2.getSelector())
                              and
                              (self.prop_names[r1.getProperty()] ==
                               self.prop_names[r2.getProperty()])) }

        cssEdgeSet = css.edgeSet - simple_masked

        if edgeSet != cssEdgeSet:
            if __DEBUG__:
                print('There are ' + str(len(edgeSet)) +' edges in edgeSet')
                print('There are ' + str(len(cssEdgeSet)) +\
                        ' edges in cssEdgeSet')
                print('There are ' + str(len(edgeSet - cssEdgeSet)) +\
                        ' edges in edgeSet - cssEdgeSet')
                print('There are ' + str(len(cssEdgeSet - edgeSet)) +\
                        ' edges in cssEdgeSet - edgeSet')
                print('Edges missing from clique: ' +\
                        str(cssEdgeSet - edgeSet))
                print('Edges missing from simple css: ' +\
                        str(edgeSet - cssEdgeSet))
            return False

        last_occurence = dict()
        i = 0
        lo_to_bucket = dict()
        j = 0
        for (ss, pp) in self.cliques:
            for p in pp:
                for s in ss:
                    e = Sim.simpleRule(s, p)
                    last_occurence[e] = i
                    lo_to_bucket[i] = j
                    i += 1
            j += 1

        for (e1, e2) in css.edgeOrder:
            if e1 in cssEdgeSet and e2 in cssEdgeSet:
                # TODO: fix so edges can be in same bucket as long as they can be
                # ordered
                if not last_occurence[e1] < last_occurence[e2]:
                    print("Edge ", e1, " last appears at property position", last_occurence[e1])
                    print("Edge ", e1, " last appears at bucket", \
                    lo_to_bucket[last_occurence[e1]])
                    print(self.cliques[lo_to_bucket[last_occurence[e1]]])
                    print("Edge ", e2, " last appears at property position", last_occurence[e2])
                    print("Edge ", e2, " last appears at bucket", \
                    lo_to_bucket[last_occurence[e2]])
                    print(self.cliques[lo_to_bucket[last_occurence[e2]]])
                    print("But the first should appear before the second!")
                    return False

        return True


    def no_conflicts(self, conflicts):
        """
        :param conflicts:
            A set of pairs (e1, e2) of simpleRules
        :returns:
            True iff no (e1, e2) in conflicts has e1 and e2 in the same bucket
        """
        for (e1, e2) in conflicts:
            for (ss, pp) in self.cliques:
                if (e1.getSelector() in ss and
                    e2.getSelector() in ss and
                    e1.getProperty() in pp and
                    e2.getProperty() in pp):
                    return False
        return True

    def __str__(self):
        bits = ["\n".join(self.ignored_rules), "\n"]
        counter = 0
        for (ss, pp) in self.cliques:
            bits.append("/* Rule number " + str(counter) + " */\n")
            bits.append(",\n".join(ss))
            bits.append(" {\n    ")
            #print pp
            bits.append(";\n    ".join(pp))
            bits.append("\n}\n\n")
            counter += 1

        return ''.join(bits)

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __iter__(self):
        """Iterates over pairs (ss, pp) of a set of selectors and properties
        in same format as in simpleRule"""
        return iter(self.cliques)

def main():
    r1 = Sim.simpleRule('A','1')
    r2 = Sim.simpleRule('A','4')
    r3 = Sim.simpleRule('A','7')
    r4 = Sim.simpleRule('B','1')
    r5 = Sim.simpleRule('B','4')
    r6 = Sim.simpleRule('C','4')
    r7 = Sim.simpleRule('C','5')
    r8 = Sim.simpleRule('C','7')
    r9 = Sim.simpleRule('D','3')
    r10 = Sim.simpleRule('D','5')
    r11 = Sim.simpleRule('D','6')
    r12 = Sim.simpleRule('E','2')
    r13 = Sim.simpleRule('E','3')
    r14 = Sim.simpleRule('E','6')
    r15 = Sim.simpleRule('E','7')
    r16 = Sim.simpleRule('F','2')
    r17 = Sim.simpleRule('F','7')
    CSS = Sim.simpleCSS([ eval('r'+str(i)) for i in range(1,18)],[(r1,r2),(r2,r3)])
    clique = cliqueCSS()
    clique.add_rule({r1.getSelector()},[r1.getProperty()])
    clique.add_rule({r3.getSelector()},[r3.getProperty()])
    clique.add_rule({r2.getSelector()},[r2.getProperty()])
    assert clique.is_sub_css(CSS), 'something wrong'

if __name__ == '__main__':
        main()
