
import bisect
from collections import defaultdict
from operator import itemgetter
from itertools import product


def safe_trim(css, colored_edges):
    """
    Trims CSS in place by identifying redundant edges.

    :param css:
        a cliqueCS)
    :param colored_edges:
        edges (as pairs) from edgeOrder from the original CSS file
    :return:
        number of nodes removed
    """

    def build_hash_table():
        """
        build a hash table
        :return:
            the constructed defaultdict(set)
        """
        hash_table = defaultdict(set)
        counter = 0
        for bucket in css:
            (ss,pp) = bucket
            for (s, p) in product(ss, pp):
                hash_table[(s,p)].add(counter)
            counter += 1
        return hash_table


    hash_table = build_hash_table()

    def is_redundant_ruleSet(ruleSet,lb):
        """
        Check if *all* rules in ruleSet can be removed. This means that
        they appear in buckets whose ids are greater than lb (lower bound,
        an integer). Each rule is a tuple (s,p) [not a simpleRule!]

        pre-condition: hash_table must have been built, lb >= 0
        """
        assert lb >= 0, "Precondition not met"

        for (s,p) in ruleSet:
            if (s,p) in colored_edges:
                if max(hash_table[(s,p)]) <= lb:
                    return False
            else:
                # should contain at least two guys
                if len(hash_table[(s,p)]) <= 1:
                    return False

        return True

    def uniq(List):
        """
        :param List:
            an input list
        :returns:
            a pair of list and how many duplicates removed. The output
            list with duplicates removed (but order maintained)
        """
        counter = 0
        output = []
        for x in List:
            if x not in output:
                output.append(x)
            else:
                counter += 1
        return (output,counter)

    def update_hash_table(ruleSet, counter):
        """
            remove counter from hash_table[rule] for every rule in ruleSet
        """
        for rule in ruleSet:
            hash_table[rule].remove(counter)

    def compute_rem_options():
        counter = 0
        rem_options = defaultdict(int)
        rem_options_wit = defaultdict(set)

        for bucket in css:
            (ss,pp) = bucket
            ss_copy = set(ss)
            pp_copy = list(pp)
            for s in ss_copy:
                ruleSet = { (s,p) for p in pp }
                if is_redundant_ruleSet(ruleSet,counter):
                    # 0 is an initial value
                    rem_options[('s',s,counter)] = 0
                    rem_options_wit[('s',s,counter)] = ruleSet
            for p in pp_copy:
                ruleSet = { (s,p) for s in ss }
                if is_redundant_ruleSet(ruleSet,counter):
                    rem_options[('p',p,counter)] = 0
                    rem_options_wit[('p',p,counter)] = ruleSet
            counter += 1

        # update the scores
        Opts = list(rem_options.keys())
        for opt in rem_options:
            (t,name,j) = opt
            #assert isinstance(name,str), "name is" + str(type(name))
            rem_options[opt] += len(name)
            ruleSet = rem_options_wit[opt]
            for opt1 in Opts:
                (_,name1,j1) = opt1
                ruleSet1 = rem_options_wit[opt1] & ruleSet
                for rule in ruleSet1:
                    assert hash_table[rule] > 1
                    assert j in hash_table[rule], str(j)
                    assert j1 in hash_table[rule], str(j1)
                    rem_options[opt1] -= 1/float(len(hash_table[rule])-1) * \
                                            len(name)

        return (rem_options,rem_options_wit)

    def delete_from_css(t,tname,index):
        """
        :param t:
            type ('s' or 'p', which stands for selector/property)
        :param tname:
            a string/unicode denoting the name of the type
        :param index:
            which bucket
        """
        (ss,pp) = css.cliques[index]
        if t == 's':
            ss.remove(tname)
        elif t == 'p':
            pp.remove(tname)
        else:
            assert False




    # remove redundant selectors/properties
    node_removed = 0
    while True:
        (rem_options,rem_options_wit) = compute_rem_options()
        if len(rem_options) == 0:
            break
        best_opt = max(iter(rem_options.items()),key=itemgetter(1))[0]
        (t,tname,i) = best_opt
        ruleSet = rem_options_wit[best_opt]
        update_hash_table(ruleSet,i)
        delete_from_css(t,tname,i)
        node_removed += 1


    # remove empty buckets
    buckets_removed = 0
    to_delete = []
    for idx, bucket in enumerate(css):
        (ss,pp) = bucket
        if len(ss) == 0 or len(pp) == 0:
            buckets_removed += 1
            bisect.insort(to_delete, idx)
    for idx in reversed(to_delete):
        css.remove_rule(idx)

    # remove duplicate properties in a bucket
    duplicates_removed = 0
    for bucket in css:
        (ss,pp) = bucket
        (pp_uniq,pp_duplicates) = uniq(pp)
        pp = pp_uniq
        duplicates_removed += pp_duplicates

    print('The number of nodes removed by safe_trim is', node_removed)
    print('The number of buckets removed by safe_trim is', buckets_removed)
    print('The number of local property duplicates removed by safe_trim is', \
            duplicates_removed)

    return node_removed

