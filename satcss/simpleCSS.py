"""simpleCSS.py
This is a stub for the simpleCSS class. Not completely done yet. """

import copy
import sys
import random

import satcss.cliqueCSS as cliqueCSS
from collections import defaultdict
from itertools import product

from toposort import toposort_flatten

__DEBUG__= False

class simpleRule(object):
    """Represents a simple CSS rule (edge)."""

    def __init__(self,sel,prop,unique=True):
        self.__selector__ = sel
        self.__property__ = prop
        self.__unique__ = unique

    def getSelector(self):
        return self.__selector__

    def getProperty(self):
        return self.__property__

    def getUnqiue(self):
        return self.__unique__

    #def revSelProp(self):
        # This is used to reverse selector and property
    #   sel = self.__selector__
    #   self.__selector__ = self.__property__
    #   self.__property__ = sel

    def getTuple(self):
        return (self.getSelector(),self.getProperty())

    def print_rule(self):
        print(str(self.__selector__) + ' { ' + str(self.__property__) + '; }')

    def print_rule_to_file(self,stream):
        stream.write( \
            str(self.__selector__) + ' { ' + str(self.__property__) + '; }\n\n')

    def __eq__(self,other):
        assert other.__class__.__name__ == 'simpleRule', '__eq__: input is' +\
                                    'not of class simpleRule'

        return (self.__selector__ == other.__selector__) & \
                (self.__property__ == other.__property__)
                # & \
                #(self.__unique__ == other.__unique__)

    def __str__(self):
        return (str(self.__selector__) +
                ' { ' + str(self.__property__) + ' }' +
                " [unique]" if self.__unique__ else " [not unique]")

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __hash__(self):
        return (hash(self.__selector__) +
                hash(self.__property__))
                #+
                #hash(self.__unique__))

class rule(object):
    """Represents a complex CSS rule (biclique of edges)."""

    def __init__(self,sels = [],props = []):
        self.__selectors__ = sels
        self.__properties__ = props

    def getSelectors(self):
        return self.__selectors__

    def getProperties(self):
        return self.__properties__

    def getAllSimpleRules(self):
        simpleRuleSet = set()
        for sel in self.__selectors__:
            for prop in self.__properties__:
                simpleRuleSet.add(simpleRule(sel,prop))

        return simpleRuleSet

    def __eq__(self,other):
        assert other.__class__.__name__ == 'rule', '__eq__: input is' +\
                                    'not of class rule'

        sels1 = set(self.__selectors__)
        props1 = set(self.__properties__)
        sels2 = set(other.__selectors__)
        props2 = set(other.__properties__)

        return sels1 == sels2 & props1 == props2

    def __contains__(self,item):
        assert item.__class__.__name__ == 'simpleRule', '__contains__: input'+\
                                    'is not of class simpleRule'

        s = item.getSelector()
        p = item.getProperty()

        return s in self.__selectors__ and p in self.__properties__

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __str__(self):
        return str(self.__selectors__) + '{' + str(self.__properties__) + '}'

    def __hash__(self):
        return sum([ hash(sel) for sel in self.__selectors__ ]) + \
            sum([ hash(prop) for prop in self.__properties__ ])

def edgeList_to_adjacencyList(edgeList):
    """
    output the adjacency list representation (i.e. dictionary) of edgeList
    """
    adj_list = defaultdict(set)
    for (x,y) in edgeList:
        adj_list[x].add(y)
        adj_list[y] # initialise

    return adj_list

def disjointEdges(edge1,edge2):
    """Check whether edge1 and edge2 are disjoint edges. Disjoint means that
    the selectors (l.h.s.) and the properties (r.h.s.) are different."""

    #Initial check
    assert edge1.__class__.__name__ == 'simpleRule', 'disjointEdges: edge1 is not simpleRule'
    assert edge2.__class__.__name__ == 'simpleRule', 'disjointEdges: edge2 is not simpleRule'

    return (edge1.__selector__ != edge2.__selector__) & \
                (edge1.__property__ != edge2.__property__)

def crossConnect(edge1,edge2,Edges):
    """Return True if edge1 and edge2 are disjoint edges and that they
    cross-connect in Edges.

    Definition: s1 { p1 } and s2 { p2 } are *cross-connected* with respect to
    a set S of edges if s1 { p2 } and s2 { p1 } are both in S.
    """

    assert edge1.__class__.__name__ == 'simpleRule', 'crossConnect: edge1 is not simpleRule'
    assert edge2.__class__.__name__ == 'simpleRule', 'crossConnect: edge2 is not simpleRule'
    #Turn this on for defensive programming
    #assert all([edge.__class__.__name__ == 'simpleRule' for edge in Edges]), \
            #'crossConnect: some element in 3rd argument is not simpleRule'

    if not disjointEdges(edge1,edge2):
        return False

    edge3 = simpleRule(edge1.__selector__,edge2.__property__)
    edge4 = simpleRule(edge2.__selector__,edge1.__property__)

    if (edge3 in Edges) and (edge4 in Edges):
        return True
    else:
        return False

def computeScore(Edges):
    """Compute the crossConnect/adjacency scores associated with each edge in
    Edges."""

    assert all([edge.__class__.__name__ == 'simpleRule' for edge in Edges]), \
            'crossConnect: some element in 3rd argument is not simpleRule'

    for edge1 in Edges:
        score = 0
        for edge2 in Edges:
            if (edge1 == edge2) or (not disjointEdges(edge1,edge2)) or \
                    (crossConnect(edge1,edge2,Edges)):
                score += 1

        edge1.score = score
        #print score

    return Edges

def minEdge(Edges):
    """Find a minimum edge in Edges. Call this only after you compute score."""

    assert all([hasattr(edge,'score') for edge in Edges]), \
            'minEdge: score is not defined'
    assert len(Edges) > 0, 'EdgeList is empty'

    edge = simpleRule('a','b') # dummy
    edge.score = sys.maxsize

    for e in Edges:
        if e.score <= edge.score:
            # Decide on tie randomly
            if e.score == edge.score and random.choice([True,False]):
                edge = e
            if e.score < edge.score:
                edge = e

    return edge

def transitive_closure(a):
    """Compute the transitive closure of the list of pairs a and output
    it as a list."""
    closure = set()
    outgoing = defaultdict(set)
    incoming = defaultdict(set)
    for (e1, e2) in a:
        outgoing[e1].add(e2)
        incoming[e2].add(e1)
    worklist = set(a)

    while len(worklist) > 0:
        (e1, e2) = worklist.pop()
        outgoing[e1].add(e2)
        incoming[e2].add(e1)
        closure.add((e1, e2))
        for e3 in outgoing[e2]:
            if not (e1, e3) in closure:
                worklist.add((e1, e3))
        for e3 in incoming[e1]:
            if not (e3, e1) in closure:
                worklist.add((e3, e1))

    return closure


def get_good_selectors(CSS):
    """
    :param CSS:
        A simple CSS file.
    :returns:
         the set of all good selectors in CSS
    """

    assert CSS.__class__.__name__ == 'simpleCSS', 'get_good_selectors: CSS is not simpleCSS'

    # Initialisation
    # badSels are used to avoid recomputation
    goodSels = set()
    badSels = set()

    #
    for sel in CSS.getSelectors():
        # badSels tells us immediately that we need not look further
        if sel not in badSels:
            neighbors = CSS.getSelectorsAdjacencyList()[sel]
            distTwo = set()
            # distTwo is the union of all prop in neighbors
            for prop in neighbors:
                distTwo.update(CSS.getPropertiesAdjacencyList()[prop])
            # Remove sel
            #distTwo.difference_update(badSels)
            distTwo.remove(sel)
            #
            goodSels.add(sel) # will be removed if bad
            for sel1 in distTwo:
                if (CSS.getSelectorsAdjacencyList()[sel]).issubset( \
                        CSS.getSelectorsAdjacencyList()[sel1]):
                    if len(sel) != len(sel1):
                        badSels.add(sel1)
                    elif sel1 in goodSels:
                        # This is an optimisation: that sel and sel1 (distance
                        # 2) have the same set of properties and sel1 is good.
                        break
                else:
                    goodSels.remove(sel)
                    badSels.add(sel)
                    break

    return goodSels




def revSelProp(CSS):
    """Output a new CSS with selectors and properties reversed (but
    no edgeOrder)."""

    assert CSS.__class__.__name__ == 'simpleCSS', 'revSelProp: CSS is not simpleCSS'

    edgeList = []
    for e in CSS.getEdgeList():
        edgeList.append(simpleRule(e.getProperty(),e.getSelector()))

    return simpleCSS(edgeList)

def get_good_properties(CSS):
    """
    :param CSS:
        A simple CSS file.
    :returns:
         the set of all good properties in CSS
    """

    assert CSS.__class__.__name__ == 'simpleCSS', 'get_good_selectors: CSS is not simpleCSS'

    assert CSS.__class__.__name__ == 'simpleCSS', 'get_good_properties: CSS is not simpleCSS'

    return get_good_selectors(revSelProp(CSS))

def get_good_edges(CSS):
    """Get good edges from CSS"""

    assert CSS.__class__.__name__ == 'simpleCSS', 'get_good_edges: CSS is not simpleCSS'

    Sels = get_good_selectors(CSS)
    Props = get_good_properties(CSS)
    Edges = set()

    for e in CSS.getEdgeList():
        if (e.getSelector() in Sels) and (e.getProperty() in Props):
            Edges.add(e)

    return Edges

def get_good_max_bicliques_and_edges(CSS):
    """
    :param CSS:
        A simple CSS file.
    :returns:
         "good" maximal bicliques and edges of CSS
    :note:
         for now only the maximal bicliques that intersect with edgeOrder
    """

    assert CSS.__class__.__name__ == 'simpleCSS', \
    'get_good_max_bicliques_and_edges: CSS is not simpleCSS'

    bicliqueSet = set()
    Edges = get_good_edges(CSS)
    EdgesNotIntersect = set()

    for e in Edges:
        props = CSS.getSelectorsAdjacencyList()[e.getSelector()]
        sels = CSS.getPropertiesAdjacencyList()[e.getProperty()]
        # Make sure that no edges in edgeOrder are in sels/props
        IsIntersect = False # flag for intersection with edgeOrder
        for e1 in CSS.getEdgesInEdgeOrder():
            if e1.getSelector() in sels and e1.getProperty() in props:
                IsIntersect = True
                break

        # For now, only add bicliques that don't intersect with edgeOrder
        if not(IsIntersect):
            EdgesNotIntersect.add(e)
            biclique = rule(sels,props)
            if biclique not in bicliqueSet:
                bicliqueSet.add(biclique)

    return (bicliqueSet,EdgesNotIntersect)

def get_good_max_bicliques(CSS):
    """
    :param CSS:
        A simple CSS file.
    :returns:
         "good" maximal bicliques and edges of CSS
    :note:
         for now only the maximal bicliques that intersect with edgeOrder
    """

    assert CSS.__class__.__name__ == 'simpleCSS', 'get_good_max_bicliques: CSS is not simpleCSS'

    (bicliqueSet,Edges) = get_good_max_bicliques_and_edges(CSS)

    return bicliqueSet

class simpleCSS(object):
    """Represents simple CSS (i.e. an ordered list of simple rules, i.e.,
    edges, and an edge order, i.e., binary tuples of simple rules)."""

    def __init__(self,
                 edgeList = [],edgeOrder = [],
                 complexRules = [], bloat = True,
                 prop_names = dict()):
        """
        :param edgeList
        :param edgeOrder
        :param complexRules
        :param bloat
            A boolean value indicating whether you want to compute everything
            that is needed to be computed (e.g. optimal representations for
            selectors/properties/adjacency list).
        :param prop_names:
            a map from properties (of the form "p: v" to the name of the
            property defined (p)
        """

        self.edgeList = edgeList
        self.edgeSet = set(edgeList)
        self.edgeOrder = set(edgeOrder)

        self.prop_names = prop_names

        if bloat:
            self.computeSelectors()
            self.computeProperties()
            self.computeAdjacencyList()
            #Decide if you want to use transitive closure
            #self.edgeOrder = edgeOrder
            self.complexRules = complexRules
            self.OptSet = set() # this is an optional set of edges: will be
                            # added by optimisation part

        # Use the following if you need to optimise with compAxioms
        self._tr_cl_edgeOrder = frozenset(transitive_closure(self.edgeOrder))

        # compute edges in edgeOrder
        edgesTemp = []
        for (e1,e2) in edgeOrder:
            edgesTemp.append(e1)
            edgesTemp.append(e2)

        self.__edges_in_edgeOrder__ = frozenset(edgesTemp)
        #print 'There are', len(self.__edges_in_edgeOrder__), 'edges in edgeOrder'
        #compute a different representation of edgeOrder
        self.order_map = defaultdict(set)
        # do we need transitive closure here?
        #for (e1, e2) in self.edgeOrder:
        for (e1,e2) in self._tr_cl_edgeOrder:
            self.order_map[e1.getTuple()].add(e2.getTuple())
            self.order_map[e2.getTuple()] # initialise

        if __DEBUG__:
            Components = self.edgeOrderComponents()
            print('********START: PRINTING edgeOrder INFORMATION*********')
            ctr = 0
            for edgeOrder1 in Components:
                print('@@@@@@ Printing edgeOrder ' + str(ctr))
                for (edge1,edge2) in edgeOrder1:
                    print('===')
                    edge1.print_rule()
                    edge2.print_rule()
                    print('===')
                print('@@@@@@ End printing edgeOrder ' + str(ctr))
                ctr += 1
            print('********END: PRINTING edgeOrder INFORMATION*********')


    def getPropName(self, p):
        """
        :param p:
            a property (of the form "p: v")
        :returns:
            the name of the property defined (p)
        """
        return self.prop_names[p]

    def getPropNames(self):
        """:returns: a map from properties (p: v) to their names (p)"""
        return self.prop_names

    def getCliqueCSS(self):
        """:returns: a cliqueCSS representing self.complexRules"""
        clique = cliqueCSS.cliqueCSS()
        for bucket in self.complexRules:
            ss = bucket.getSelectors()
            pp = bucket.getProperties()
            clique.add_rule(set(ss),pp)
#
        return clique

    def edgeOrderComponents(self):
        """:returns: an iterator over an iteration over the edges of each
        connected component.

        Note: computes components on each call, so we need to store it somewhere
        if we use it a lot.

        E.g. for component in o.edgeOrderComponent():
                 for (e1, e2) in component
                    do something with order
        """
        # Code from http://stackoverflow.com/a/13837045
        def connected_components(neighbors):
            seen = set()
            def component(node):
                nodes = set([node])
                while nodes:
                    node = nodes.pop()
                    seen.add(node)
                    nodes |= neighbors[node] - seen
                    yield node
            for node in neighbors:
                if node not in seen:
                    yield component(node)

        neighbours = defaultdict(set)
        outgoing = defaultdict(set)
        for (e1, e2) in self.edgeOrder:
            neighbours[e1].add(e2)
            neighbours[e2].add(e1)
            outgoing[e1].add((e1, e2))

        return [ [ order for e in component for order in outgoing[e] ]
                 for component in connected_components(neighbours) ]

    def isEdge(self,edge):
        return edge in self.edgeSet

    def addEdge(self,edge):
        self.edgeList.append(edge)

    def removeEdges(self,Edges):
        """Remove the set/list of edges Edges"""
        # Make sure edge does not intersect with edgeOrder for now!!

        for edge in Edges:
            assert edge not in self.getEdgesInEdgeOrder(), \
                "removeEdge: in EdgeOrder"

        for edge in Edges:
            try:
                self.edgeList.remove(edge)
            except ValueError:
                pass  # do nothing!
            self.edgeSet.discard(edge)

        # Update Selectors, Properties, and AdjacencyList
        self.computeSelectors()
        self.computeProperties()
        self.computeAdjacencyList()

    def build_edge_membership_table(self):
        """
        build an occurrence table. Make sure bloat is turned on
        """
        if hasattr(self,'edge_membership_table'):
            return

        self.edge_membership_table = defaultdict(set)
        counter = 0
        for bucket in self.complexRules:
            ss = bucket.getSelectors()
            pp = bucket.getProperties()
            for s in ss:
                for p in pp:
                    self.edge_membership_table[(s,p)].add(counter)
            counter += 1

    def partition_last_occurrence(self):
        """
        Partition the complex rules into two
        """
        non_last_rules = []
        last_rules = []
        self.build_edge_membership_table()

        # Obtain indices of last occurrence buckets
        memo = set()
        #for bucket in self.complexRules:
        for e in self.__edges_in_edgeOrder__:
            (s,p) = e.getTuple()
            last_index = max(self.edge_membership_table[(s,p)])
            memo.add(last_index)

        list_memo = list(memo)
        list_memo.sort()

        for i in list_memo:
            # not copying, just adding references here
            last_rules.append(self.complexRules[i])

        for i in range(len(self.complexRules)):
            if i not in memo:
                # not copying, just adding references here
                non_last_rules.append(self.complexRules[i])

        edgeSet1 = [ simpleRule(s,p) for cr in non_last_rules for (s,p) in \
                product(cr.getSelectors(), cr.getProperties()) ]
        edgeSet2 = [ simpleRule(s,p) for cr in last_rules for (s,p) in \
                product(cr.getSelectors(), cr.getProperties()) ]

        #print set(edgeSet1) - set(edgeSet2)
        #assert set(edgeSet1).issubset(set(edgeSet2)), "non-last-occurrence error"

        #edgeOrder2 = [ (e1,e2) for (e1,e2) in self.edgeOrder if \
                #any(e1 in cr for cr in last_rules) and \
                #any(e2 in cr for cr in last_rules) ]

        #print len(edgeSet1)
        #print len(edgeSet2)
        print(len(non_last_rules))
        print(len(last_rules))
        #assert False

        CSS1 = simpleCSS(edgeSet1,[],non_last_rules)
        CSS2 = simpleCSS(edgeSet2,self.edgeOrder,last_rules)

        return (CSS1,CSS2)

    def getEdgesInEdgeOrder(self):
        return self.__edges_in_edgeOrder__

    def getEdgeList(self):
        return copy.deepcopy(self.edgeList)

    def getEdgeSet(self):
        return self.edgeSet

    def getComplexRules(self):
        return self.complexRules

    def getSelectors(self):
        return self._selectors_

    def getProperties(self):
        return self._properties_

    def getSelectorsAdjacencyList(self):
        return self._selectorsAdjacencyList_

    def getPropertiesAdjacencyList(self):
        return self._propertiesAdjacencyList_

    def getEdgeOrder(self):
        return copy.deepcopy(self.edgeOrder)

    def getTrClEdgeOrder(self):
        return self._tr_cl_edgeOrder

    def computeSelectors(self):
        """Compute a set of selectors. Precondition: edgeSet is defined."""

        self._selectors_ = set()

        for edge in self.edgeSet:
            self._selectors_.add(edge.getSelector())

    def computeProperties(self):
        """Compute a set of properties. Precondition: edgeSet is defined."""

        self._properties_ = set()

        for edge in self.edgeSet:
            self._properties_.add(edge.getProperty())

    def computeAdjacencyList(self):
        """Compute adjacency list. Precondition: edgeSet, _selectors_,
           _properties_ are defined."""

        # Initialisation: set everything to empty dictionaries
        self._selectorsAdjacencyList_ = dict()
        self._propertiesAdjacencyList_ = dict()

        # compute the adjacency list for selectors
        for sel in self._selectors_:
            self._selectorsAdjacencyList_[sel] = \
                    set([ r.getProperty() for r in self.edgeSet \
                        if r.getSelector() == sel ])

        # compute the adjacency list for properties
        # Note: the method is symmetric
        for prop in self._properties_:
            self._propertiesAdjacencyList_[prop] = \
                    set([ r.getSelector() for r in self.edgeSet \
                        if r.getProperty() == prop ])

    def get_max_bicliques(self):
        """
        :returns:
            the maximal bicliques of simpleCSS.edgeList as a set of pairs
            (S, P) where S is a set of selectors from simpleRules and P is a set of
            properties from simpleRule.  Only returns those where S and P are non-empty.
        """
        # Implements algorithm from
        # On enumerating all maximal bicliques of bipartite graphs
        # Enver Kayaaslan
        # http://www.academia.edu/1612454/On_Enumerating_All_Maximal_Bicliques_of_Bipartite_Graphs

        neighbours = defaultdict(set)
        for e in self.edgeList:
            neighbours[e.getSelector()].add(e.getProperty())
            neighbours[e.getProperty()].add(e.getSelector())

        props = { r.getProperty() for r in self.edgeList }

        consensus = {}
        def get_consensus(ss):
            if ss in consensus:
                return consensus[ss]
            else:
                con = props
                for s in ss:
                    con = con.intersection(neighbours[s])
                fcon = frozenset(con)
                consensus[ss] = fcon
                return fcon

        S = { frozenset(neighbours[p]) for p in props }
        Q = list(S)
        while len(Q) > 0:
            ss = Q.pop()
            for p in props - get_consensus(ss):
                ss_new = frozenset(ss.intersection(neighbours[p]))
                if not ss_new in S:
                    S.add(ss_new)
                    Q.append(ss_new)

        bicliques = { (ss, get_consensus(ss)) for ss in S }
        return { (ss, pp)
                 for (ss, pp) in bicliques
                 if len(ss) > 0 and len(pp) > 0 }


    def is_orderable_biclique(self, ss, pp, ignore_rules = set()):
        """
        :param ss:
            A set of selectors in the same format as simpleRule
        :param pp:
            A set of properties in the same format as simpleRule
        :param ignore_rules:
            A set of simpleRule
        :returns:
            True iff biclique is orderable wrt all rules except those in ignore_rules, else False
        """
        order = self.order_properties(ss, pp, ignore_rules)
        return order is not None

    def _related_properties(self, p1, p2):
        """
        :param p1:
            A property as a string "name: value"
        :param p2:
            A property as a string "name: value"
        :returns:
            True if the order of p1 and p2 is meaningful.  That is they
            both refer to the same property name, or one property name
            is shorthand for the other.
        """
        name1 = p1.split(':')[0]
        name2 = p2.split(':')[0]
        from satcss.simplecssbuilder import related_props
        return related_props(name1, name2)

    def get_orderable_sub_max_bicliques(self, ss, pp, ignore_rules = set(), max_split = -1):
        """
        :param ss:
            A set of selectors in the same format as simpleRule
        :param pp:
            A set of properties in the same format as simpleRule
        :param ignore_rules:
            A set of simpleRule that can be ignored when calculating if a
            biclique is orderable
        :param max_split:
            If > 0 then generate at most max_split sub bicliques and then simply
            stop generating anymore (to avoid exponential sinks)
        :returns:
            An iteration of non-empty sub max bicliques that are orderable (may
            contain duplicates)
        """

        # Calculate which selectors and properties have any effect on
        # unorderability

        tran_order = self.getTrClEdgeOrder()
        ordered_edges = self.getEdgesInEdgeOrder()

        cand_s = set()
        cand_p = set()

        # nodes involved in enforcing some p1 < p2
        for (s1, p1) in product(ss, pp):
            e1 = simpleRule(s1, p1)
            if e1 in ordered_edges and not e1 in ignore_rules:
                for (s2, p2) in product(ss, pp):
                    e2 = simpleRule(s2, p2)
                    if e1 != e2 and e2 in ordered_edges and not e2 in ignore_rules:
                        cand_s.add(s1)
                        cand_s.add(s2)
                        cand_p.add(p1)
                        cand_p.add(p2)

        return self.__orderable_sub_max_bicliques_cand(ss, pp, cand_s, cand_p, ignore_rules, max_split)





    def order_properties(self, ss, pp, ignore_rules = set()):
        """
        :param ss:
            A set of selectors in the same format as simpleRule
        :param pp:
            A set of properties in the same format as simpleRule
        :param ignore_rules:
            a set of simpleRule
        :returns:
            None if (ss, pp) is not orderable wrt edges not in ignore_rules
            or pp' where pp' is a list of properties is the order they should
            appear in the file
        """
        order = set()
        ordered_edges = self.getEdgesInEdgeOrder()
        tran_order = self.getTrClEdgeOrder()

        # first compute direct p1 < p2
        for (p1, p2) in product(pp, pp):
            if (p1 != p2 and
                (p1, p2) not in order and
                self._related_properties(p1, p2)):

                for s1 in ss:
                    e1 = simpleRule(s1, p1)
                    if e1 in ordered_edges and e1 not in ignore_rules:
                        for s2 in ss:
                            e2 = simpleRule(s2, p2)
                            if e2 not in ignore_rules and (e1, e2) in tran_order:
                                if (p2, p1) in order:
                                    return None
                                else:
                                    order.add((p1, p2))
                                    break

        # then take the transitive closure
        closure = set()
        outgoing = defaultdict(set)
        incoming = defaultdict(set)
        for (p1, p2) in order:
            outgoing[p1].add(p2)
            incoming[p2].add(p1)
        worklist = set(order)

        while len(worklist) > 0:
            (p1, p2) = worklist.pop()
            if (p2, p1) in closure:
                return None
            outgoing[p1].add(p2)
            incoming[p2].add(p1)
            closure.add((p1, p2))
            for p3 in outgoing[p2]:
                if not (p1, p3) in closure:
                    worklist.add((p1, p3))
            for p3 in incoming[p1]:
                if not (p3, p1) in closure:
                    worklist.add((p3, p1))

        # since we didn't catch anything earlier, we have an ordering
        order_map = defaultdict(set)
        for (p1, p2) in closure:
            order_map[p2].add(p1)

        prop_ord = toposort_flatten(order_map)
        unordered_props = pp - set(prop_ord)
        prop_ord += unordered_props

        return prop_ord


    def print_all_rules(self):
        for edge in self.edgeList:
            edge.print_rule()

    def print_all_rules_to_file(self,stream):
        for edge in self.edgeList:
            edge.print_rule_to_file(stream)


    def __str__(self):
        return ("Edges:\n\n" +
                '\n'.join(map(str, self.edgeList)) +
                "\n\nOrder:\n\n" +
                '\n'.join([str(x_y[0]) + " < " + str(x_y[1]) for x_y in self.edgeOrder]) +
                "\n\nComplex Rules:\n\n" +
                "\n".join(map(str, self.complexRules)))

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __eq__(self, other):
        """Slightly inefficient equality method for testing purposes"""
        return (other.__class__.__name__ == self.__class__.__name__ and
                set(self.edgeList) == set(other.edgeList) and
                set(self.edgeOrder) == set(other.edgeOrder) and
                set(self.complexRules) == set(other.complexRules))

    def __orderable_sub_max_bicliques_cand(self, ss, pp, cand_s, cand_p, ignore_rules = set(), max_split = -1):
        """
        :param ss:
            A set of selectors in the same format as simpleRule
        :param pp:
            A set of properties in the same format as simpleRule
        :param cand_s:
            A set of selectors in the same format as simpleRule
        :param cand_p:
            A set of properties in the same format as simpleRule
        :param ignore_rules:
            A set of simpleRule that can be ignored when calculating if orderable
        :param max_split:
            If > 0 then generate at most max_split sub bicliques and then simply
            stop generating anymore (to avoid exponential sinks)
        :returns:
            An iteration of non-empty sub max bicliques that are orderable (may
            contain duplicates) given a sets of candidate sels and props to
            remove from (ss, pp) that might result in an orderable max biclique
        """
        not_enough_s = set()
        for s in cand_s:
            if max_split == 0:
                return

            ss1 = set(ss)
            ss1.remove(s)
            if self.is_orderable_biclique(ss1, pp, ignore_rules):
                max_split -= 1
                yield (frozenset(ss1), frozenset(pp))
            else:
                not_enough_s.add(s)

        not_enough_p = set()
        for p in cand_p:
            if max_split == 0:
                return

            pp1 = set(pp)
            pp1.remove(p)
            if self.is_orderable_biclique(ss, pp1, ignore_rules):
                max_split -= 1
                yield (frozenset(ss), frozenset(pp1))
            else:
                not_enough_p.add(p)

        # Now try removing more than one element, but no point removing elements
        # that we know are enough on their own

        new_cand_s = cand_s - not_enough_s
        new_cand_p = cand_p - not_enough_p

        for s in not_enough_s:
            if max_split == 0:
                return

            ss1 = set(ss)
            ss1.remove(s)
            for (ss2, pp2) in self.__orderable_sub_max_bicliques_cand(ss1, pp,
                                                                      new_cand_s,
                                                                      new_cand_p,
                                                                      ignore_rules,
                                                                      max_split):
                max_split -= 1
                yield (frozenset(ss2), frozenset(pp2))

        for p in not_enough_p:
            if max_split == 0:
                return

            pp1 = set(pp)
            pp1.remove(p)
            for (ss2, pp2) in self.__orderable_sub_max_bicliques_cand(ss, pp1,
                                                                      new_cand_s,
                                                                      new_cand_p,
                                                                      ignore_rules,
                                                                      max_split):
                max_split -= 1
                yield (frozenset(ss2), frozenset(pp2))


def CIL(CSS):
    """Compute a cross independent list (CIL) of edges in CSS (i.e. of class
    simpleCSS). A list L of edges is *cross independent* if each edge in L
    satisfies the following condition:
    1) not in CSS.getEdgesInEdgeOrder() and CSS.OptSet
    2) disjoint (in the sense of disjointEdges function above) with any edge in
        CSS.getEdgesInEdgeOrder() or any other edges in L
    3) not cross-connected (see below for definition) to any edge in
        CSS.getEdgesInEdgeOrder() or any other edges in L

    The computation of L is done by heuristics, i.e., a greedy algorithm that
    is similar to that for maximum independent set.

    Definition: s1 { p1 } and s2 { p2 } are *cross-connected* with respect to
    a set S of edges if s1 { p2 } and s2 { p1 } are both in S. If S is not
    mentioned, then it is assumed to be CSS.EdgeList
    """

    assert CSS.__class__.__name__ == 'simpleCSS', 'CIL: CSS is not simpleCSS'

    # Get EdgeList minus EdgeOrder
    E = set(CSS.getEdgeList())
    E1 = CSS.getEdgesInEdgeOrder()
    E.difference_update(E1)
    E.difference_update(CSS.OptSet) # Now E satisfies (1)

    # Compute a maximum subset S1 of E satisfying 2 (a) and 3 (a) and 1
    S1 = set()
    for edge in E:
        if all([disjointEdges(edge,edge1) for edge1 in E1]):
            if all([not crossConnect(edge,edge1,E) for edge1 in E1]):
                S1.add(edge)

    # Compute a subset S of S1 additionally satisfying 2(b) and 3(b)
    # This is done using a greedy algorithm
    S = set()
    S2 = computeScore(copy.deepcopy(S1))
    while len(S2) > 0:
        edge = minEdge(S2)
        #assert edge in S1, "CIL: something really wrong"
        S.add(copy.deepcopy(edge))
        # Remove all the edges in S1 cross-connected to edge
        #STemp = set() # Use a temporary S
        for edge1 in list(S2):
            if (edge1 == edge) or (not disjointEdges(edge1,edge)) or \
                    (crossConnect(edge1,edge,E)):
                S2.remove(edge1)
        #S1 = STemp

    #if __DEBUG__:
        #print 'There are ' + str(len(S)) + ' edges in S'
        #for edge in S:
            #edge.print_rule()

    return S

def main():
    r1 = simpleRule('s1','p1')
    r2 = simpleRule('s2','p2')
    r3 = simpleRule('s3','p2')
    r4 = simpleRule('s4','p3')
    r5 = simpleRule('s2','p3')
    r6 = simpleRule('s4','p2')
    cr = rule(['s1','s2'],['p1','p2'])
    print(r1 in cr)
    """CSS = simpleCSS([r1,r2,r3,r4,r5,r6],[(r1,r4)])
    for edge in CIL(CSS):
        edge.print_rule()
    print 'END'
    CSS.print_all_rules()
    print disjointEdges(r1,r2) # disjoint
    print disjointEdges(r2,r3) # not disjoint
    print disjointEdges(r1,r4) # not disjoint
    print CSS.isEdge(r4)
    #edgeList = CSS.getEdgeList()
    #print edgeList
    #print CSS.edgeList
    #for edge in edgeList:
        #edge.print_rule()"""

if __name__ == '__main__':
    main()
