"""A simple class to hold a refactoring.  A refactoring is a rule that should be
inserted into a cliqueCSS and the trim_file is called.  Can use a
Refactoring.apply(cliqueCSS) to do this in one call.  Can use trim_file
independently."""

import bisect

from satcss.simpleCSS import simpleRule


def trim_file(clique):
    """Removes nodes (selectors or properties) from cliques if all incident
    edges are not the final instance of that edge in the file.

    :param clique:
        A cliqueCSS that will be trimmed in place
    :returns:
        Number of nodes removed
    """
    last_index = clique.build_last_index_map()
    removed = 0

    # remove nodes
    for (i, (ss, pp)) in enumerate(clique):
        s_to_del = []
        for s in ss:
            removable = True
            for p in pp:
                if last_index[simpleRule(s, p)] == i:
                    removable = False
                    break
            if removable:
                s_to_del.append(s)

        p_to_del = []
        for p in pp:
            removable = True
            for s in ss:
                if last_index[simpleRule(s, p)] == i:
                    removable = False
                    break
            if removable:
                p_to_del.append(p)

        for s in s_to_del:
            ss.remove(s)
        for p in p_to_del:
            pp.remove(p)

        removed += len(s_to_del) + len(p_to_del)

    # remove empty buckets
    to_del = []
    for (i, (ss, pp)) in enumerate(clique):
        if len(ss) == 0 or len(pp) == 0:
            bisect.insort(to_del, i)
    for i in reversed(to_del):
        clique.remove_rule(i)

    return removed



class Refactoring:
    """A class with

    :field insertions:
        A list of tuples (idx, self, props) representing inserting bucket (sels,
        props) into position idx, where
        :idx:
            An index integer denoting the bucket to insert the new rule in front of
            (e.g. 0 means before first bucket)
        :sels:
            A set of selectors in the same format as cliqueCSS
        :props:
            A list of properties in the same format as cliqueCSS
    :field size:
        The estimated size of the file after the refactoring, or -1 if no estimate available
    """
    def __init__(self, insertions, size):
        self.insertions = insertions
        self.size = size

    def __repr__(self):
        return "Id: " + repr(id(self)) + "\n" + str(self)

    def __str__(self):
        return ("\n".join(["(" +
                           str(sels) + ", " +
                           str(props) + ")@" +
                           str(idx)
                           for (idx, sels, props) in self.insertions ]) +
                "\nsize " + str(self.size))

    def apply(self, clique):
        """Applies the refactoring to the given cliqueCSS.

        :param clique:
            A cliqueCSS to apply the refactoring to.
        :returns:
            The number of nodes removed by the refactoring.
        """
        for (idx, sels, props) in self.insertions:
            clique.insert_rule(idx, sels, props)

        return trim_file(clique)

