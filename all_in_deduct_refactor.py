"""A function for encoding the refactoring finding problem as a single weighted
constraint solving problem and returning the best solution found."""

from enum import Enum
from collections import defaultdict
from timeit import default_timer
from itertools import product

import z3
import cmdZ3Wrapper
import wcnfWrapper

_z3 = cmdZ3Wrapper

from z3int import Z3BinInt
from simpleCSS import simpleRule
from refactoring import Refactoring
from cnflib import *

MAX_SPLIT_FACTOR = 0#.3

class RefactoringType(Enum):
    """The one that saves the most bytes"""
    best = 0
    """Any that respects edgeOrder, but may make the CSS larger"""
    any = 1
    """Any that reduces size"""
    good = 2


# Use the same optimizer throughout, but .push() before and .pop() after use
_optimizer = None

def get_optimizer():
    global _optimizer
    if _optimizer is None:
        _optimizer = _z3.Optimize()
        _optimizer.set('maxsat_engine', 'wmax')
    return _optimizer


class _PseudoOptimizer(object):
    """A fake optimizer to collect weighted constraints and then simply assert
    the weight satisfies a condition"""

    def __init__(self):
        self._clauses = []
        self._weight_vars = []
        self._next_var = 0
        self._weight = _z3.Int("solution_weight")

    def add_soft(self, fmla, weight):
        """Adds a soft constraint to the "solver"
        :param clause:
            A Z3 fmla
        :param weight:
            The cost of violating the formula
        :returns:
            Some pseudo handle.  Just None for now, but can extend to get value
            of self._weight in the future.
            TODO: extend as above.
        """
        var = self._make_var()
        self._clauses.append(_z3.Or(_z3.Not(fmla), var == 0))
        # not fmla => var=weight
        self._clauses.append(_z3.Or(fmla, var == weight))
        self._weight_vars.append(var)
        return None

    def add(self, fmla):
        """Adds a hard constraint to the "solver"
        :param clause:
            A Z3 fmla
        """
        self._clauses.append(fmla)

    def _make_var(self):
        self._next_var += 1
        return _z3.Int("fake_weight_" + str(self._next_var))

    def get_weight_var(self):
        """:returns: the variable as Z3 Int which will hold the weight of a
        solution.  Can use this to add constraints on the weight of a
        solution."""
        return self._weight

    def get_constraint(self):
        """:returns: a Z3 formula asserting that the weight variable correctly
        reflects the weight of the solution.  Must be asserted in the solver."""
        return _z3.And(_z3.And(self._clauses),
                       self._weight == _z3.Sum(self._weight_vars))

def all_in_find_refactoring(clique, simple,
                            timebound,
                            ref_type,
                            partition, num_partitions,
                            child_collector = None):
    """Find a refactoring to apply to clique

    :param clique:
        A cliqueCSS
    :param simple:
        A simpleCSS equivalent to clique
    :param timebound:
        A bound on calls to Z3
    :param ref_type:
        RefactoringType value for which type of refactoring to find
    :param partition:
        Integer.  Search only max bicliques with this index, modulo
        num_partitions.
    :param num_partitions:
        Integer.  See above.
    :param child_collector:
        a ChildCollector used in multi-threaded mode to allow started
        instances of z3 to be tracked and reliably terminated.  Or None
        if not being used.
    :return:
        A Refactoring object giving a clique to add at a given position, or
        None if none found
    """
    global _z3

    # Have to do this here because of import deps -- apologies for hackiness!
    from main import get_dimacs_output
    if get_dimacs_output():
        _z3 = wcnfWrapper
    optimizer = get_optimizer()

    optimizer.push()

    print("Building encoding...")
    from main import get_no_bicliques
    start_t = default_timer()
    encoder = (_Z3EncoderBiclique(clique, simple, partition, num_partitions)
               if not get_no_bicliques()
               else _Z3EncoderSimple(clique, simple, partition, num_partitions))

    encoder.add_hard_constraints(optimizer)
    # TODO: find out how to make this work
    # optimizer.set('timeout',timebound)

    handle = None
    if ref_type == RefactoringType.best:
        handle = encoder.add_soft_constraints(optimizer)
    elif ref_type == RefactoringType.good:
        pseudo = _PseudoOptimizer()
        encoder.add_soft_constraints(pseudo)
        optimizer.add(pseudo.get_constraint())
        optimizer.add(pseudo.get_weight_var() < clique.size())

    encoder.add_final_constraints(optimizer)

    end_t = default_timer()
    print("Building encoding took", (end_t - start_t), "s")

    print("Checking...")
    start_t = default_timer()
    res = optimizer.check(child_collector)
    end_t = default_timer();
    print("Checking took", (end_t - start_t), "s")

    size = clique.size()

    refactoring = None
    if res == _z3.sat:
        refactoring = encoder.get_refactoring(optimizer.model(), handle)

    optimizer.pop()

    return refactoring


def _add_independent_refactoring(refactoring1, refactoring2, size):
    """Adds refactoring2 to refactoring1 on the assumption that the buckets in
    refactoring2 do not contain any edges from refactoring1

    :param refactoring1:
        A Refactoring to add to
    :param refactoring2:
        A Refactoring to add from
    :param size:
        the .size() of the cliqueCSS the refactoring will be applied to
    """
    refactoring1.insertions.extend(refactoring2.insertions)

    saving1 = size - refactoring1.size
    saving2 = size - refactoring2.size

    refactoring1.size = size - saving1 - saving2


class _Z3EncoderBiclique(object):
    """Encodes the problem of identifying a refactoring as a Z3 formula.
       Uses max biclique enumeration technique.
       Note: only searches for a single bucket to insert"""

    # TODO: sort out private field naming convention!

    def __init__(self, clique, simple, partition, num_partitions):
        """
        :param clique:
            The cliqueCSS to optimise
        :param simple:
            A simpleCSS equivalent to the cliqueCSS
        :param partition:
            Integer.  Search only max bicliques with this index, modulo
            num_partitions.
        :param num_partitions:
            Integer.  See above.
        """
        self.clique = clique
        self.simple = simple

        # positions to insert biclique
        self.idx = CNFInt("idx", self.clique.num_rules() + 1, _z3)

        # need to know last index of all edges to calculate savings and if edge
        # order respected
        self.last_index = clique.build_last_index_map()

        print("Getting bicliques...")
        start_t = default_timer()

        from main import get_unlim_bicliques
        split_factor = -1 if get_unlim_bicliques() else MAX_SPLIT_FACTOR

        (max_bicliques, forbidden) = clique.get_orderable_max_bicliques(simple, split_factor)
        end_t = default_timer()
        print("Getting bicliques took", (end_t - start_t), "s")

        parity_bicliques = [ bc
                             for (i, bc) in enumerate(max_bicliques)
                             if i % num_partitions == partition ]
        self.forbidden = forbidden

        # map from max bicliques to index of second bucket containing an edge
        # from that biclique (only for max bicliques that have such an index)
        self.second_index = self.__build_second_index_map(parity_bicliques)

        # only need bicliques that actually have a second index
        self.bicliques = [ bc for bc in self.second_index.keys() ]
        self.nbicliques = len(self.bicliques)

        # variables for inserted buckets
        self.bvar = CNFInt("biclique", self.nbicliques, _z3)

        # Dict from edges/sels/props to bicliques containing the edge
        self.edgebcs = defaultdict(set)
        self.s_bcs = defaultdict(set)
        self.p_bcs = defaultdict(set)
        for (ss, pp) in self.bicliques:
            for s in ss:
                self.s_bcs[s].add((ss, pp))
            for p in ss:
                self.p_bcs[s].add((ss, pp))
            for s in ss:
                for p in pp:
                    self.edgebcs[(s, p)].add((ss, pp))

        self.bidxs = { self.bicliques[i] : i
                       for i in range(self.nbicliques) }

        sel_ex = { e1.getSelector() for (e1, e2) in self.simple.edgeOrder }
        prop_ex = { e1.getProperty() for (e1, e2) in self.simple.edgeOrder }

        self.s_excls = {}
        self.p_excls = {}
        self.max_s_i = 0
        self.max_p_i = 0

        from main import get_full_exclusion
        full_ex = get_full_exclusion()

        for (ss, pp) in self.bicliques:
            sels = None
            props = None
            if full_ex:
                sels = list(ss)
                props = list(pp)
            else:
                sels = list(sel_ex.intersection(ss))
                props = list(prop_ex.intersection(pp))

            self.max_s_i = max(self.max_s_i, len(sels))
            self.max_p_i = max(self.max_p_i, len(props))
            s_m = { sels[i] : i for i in range(len(sels)) }
            p_m = { props[i] : i for i in range(len(props)) }
            self.s_excls[(ss, pp)] = s_m
            self.p_excls[(ss, pp)] = p_m

        # The exclusion vars: ex_s_vars[(i, j)] means selector j does not appear
        # in bucket i (where the jth selector depends on the chosen biclique for
        # that bucket)
        self.ex_s_vars = [ _z3.Bool("ex_s(" + str(j) + ")")
                           for j in range(self.max_s_i) ]
        self.ex_p_vars = [ _z3.Bool("ex_p(" + str(j) + ")")
                           for j in range(self.max_p_i) ]

        # some memoisation
        self.__has_edge_memo = dict()


    def add_hard_constraints(self, optimizer):
        """Add a formula putting required constraints on get_soft_constraints

        :param optimizer:
            A Z3 Optimizer to add hard constraints to
        """
        self.__add_indices_in_bounds_fmla(optimizer)
        self.__add_refactor_respects_order(optimizer)

        self.__add_biclique_in_range(optimizer)
        self.__add_biclique_position_range(optimizer)
        # self.__add_biclique_restrict_positions(optimizer)

        self.__add_exclude_only_in(optimizer)


    def add_soft_constraints(self, optimizer):
        """Add formulas that needs to be maximised to find the best refactoring.
           Relies on get_constraints() also being asserted

        :param optimizer:
            A Z3 Optimize to add soft constraints to
        :return:
            A handle to the soft constraints
        """
        return self.__add_count_size(optimizer)


    def add_final_constraints(self, optimizer):
        """Adds final constraints that should be asserted after all others have been added.

        :param optimizer:
            A Z3 Optimize to add the constraints to
        """
        for c in self.idx.get_variable_constraints():
            optimizer.add(c)
        for c in self.bvar.get_variable_constraints():
            optimizer.add(c)


    def get_refactoring(self, model, handle):
        """Returns the refactoring corresponding to the model found by Z3

        :param model:
            The model returned by Z3 .model()
        :param handle:
            A Z3 handle to the soft constraints or None if not available
            (refactoring will not indicate file size after refactoring)
        :returns:
            A new Refactoring or None if the solution is an empty refactoring
            (i.e. no saving)
        """

        insertions = []

        biclique_num = self.bvar.get_value(model)

        (ss, pp) = self.bicliques[biclique_num]
        (ss_res, pp_res) = (set(ss), set(pp))

        # remove excluded selectors
        s_excl = self.s_excls[(ss, pp)]
        for s in s_excl:
            j = s_excl[s]
            if _z3.is_true(model[self.ex_s_vars[j]]):
                ss_res.remove(s)

        # remove excluded properties
        p_excl = self.p_excls[(ss, pp)]
        for p in p_excl:
            j = p_excl[p]
            if _z3.is_true(model[self.ex_p_vars[j]]):
                pp_res.remove(p)

        idx = self.__get_index(model)

        ignore_rules = self.clique.get_edge_set(idx)

        ord_pp_res = self.simple.order_properties(ss_res, pp_res, ignore_rules)

        if ord_pp_res is None:
            print("Dang, we got an unorderable one")
            print(pp_res)
            print(" at pos ", idx, "forbidden at idx is")
            print(self.forbidden[idx])
            print(" and before ")
            print(self.forbidden[idx - 1])
            print(" ahd after ")
            print(self.forbidden[idx + 1])
            exit(-1)

        # create new bucket
        if len(ss_res) > 0 and len(pp_res) > 0:
            insertions.append((idx, ss_res, ord_pp_res))

        size = self.__get_size(handle)

        if len(insertions) > 0:
            return Refactoring(insertions, size)
        else:
            return None


    def __build_second_index_map(self, bicliques):
        """
        :param bicliques:
            Set of bicliques (ss, pp) to build map for
        :returns:
            A map from max bicliques of simple to the second bucket in
            clique that contains an edge of the max biclique.
            Only defined for max bicliques satisfying such a property
        """
        second_index_map = dict()

        first_index = self.clique.build_first_index_map()

        for (ss, pp) in bicliques:
            min_idxs = set(first_index[simpleRule(s, p)]
                           for (s, p) in product(ss, pp))
            if len(min_idxs) > 1:
                min_idxs.remove(min(min_idxs))
                second_index_map[(ss, pp)] = min(min_idxs)

        return second_index_map

    def __get_index(self, model):
        """
        :param model:
            A Z3 model of the constructed formula
        :returns:
            The index of the ith bucket to insert as Integer
        """
        return self.idx.get_value(model)

    def __get_size(self, handle):
        """
        :param handle:
            The Z3 optimisation handle associated to the formula or None
        :returns:
            The size of the CSS after the refactoring associated to handle
            or -1 if handle is None
        """
        if handle is None:
            return -1
        else:
            # TODO: this properly
            return int(str(handle.value()))

    def __add_biclique_in_range(self, optimizer):
        """Adds formula asserting bvar is num of valid biclique

        :param optimizer:
            A Z3 Optimize to add constraints to
        """
        optimizer.add(self.bvar >= 0)
        optimizer.add(self.bvar < self.nbicliques)


    def __add_biclique_restrict_positions(self, optimizer):
        """Adds constraints saying a biclique should not appear immediately
        after a rule if it does not contain any of the edges in the rule (it
        could just as well appear before the rule instead).

        :param optimizer:
            A Z3 Optimize to add constraints to
        """
        start_t = default_timer()
        for i in range(self.clique.num_rules()):
            (ss, pp) = self.clique.cliques[i]
            possible_bicliques = { self.bidxs[(ss2, pp2)]
                                   for (s, p) in product(ss, pp)
                                   for (ss2, pp2) in self.edgebcs[(s, p)] }
            # (idx == i+1) => one of possible bicliques
            clause = [ self.bvar == j for j in possible_bicliques ]
            clause.append(_z3.Not(self.idx == i+1))
            optimizer.add(_z3.Or(clause))
        end_t = default_timer()
        print("Biclique restriction took", (end_t - start_t), "s")



    def __add_biclique_position_range(self, optimizer):
        """Adds to optimizer a formula asserting that biclique i cannot appear
        before any of its edges have appeared, or more than one bucket after the
        last of its edges appears in the current CSS.

        Also asserts that the ith insertion appears after the (i-1)th

        :param optimizer:
            A Z3 Optimize instance to add to
        """
        first_index = self.clique.build_first_index_map()

        for (ss, pp) in self.bicliques:
            # have to be able to remove from at least two rules to make a
            # difference
            min_idx = self.second_index[(ss, pp)]
            max_idx = 1 + max(self.last_index[simpleRule(s, p)]
                              for (s, p) in product(ss, pp))

            # is biclique => idx > min && idx < max
            optimizer.add(_z3.Or(_z3.Not(self.__is_biclique((ss, pp))),
                                 self.idx > min_idx))
            optimizer.add(_z3.Or(_z3.Not(self.__is_biclique((ss, pp))),
                                 self.idx <= max_idx))


    def __add_clique_size(self, optimizer):
        """Adds soft constraints to subtract weight of new clique

        :param optimizer:
            The Z3 Optimize to add soft constraints to
        :returns handle:
            A Z3 handle to the soft constraints if any created, None if not
        """

        h = None

        for (ss, pp) in self.bicliques:
            s_excl = self.s_excls[(ss, pp)]
            p_excl = self.p_excls[(ss, pp)]

            size = self.clique.clique_size((ss, pp))

            # remove sels/props that might be omitted
            # subtract len(ss) because each s has trailing ,
            # and each prop has trailing ;
            # (except last, but then we also have the bucket's { and } to
            # count so it works out)
            size -= sum(map(len, s_excl)) + len(s_excl)
            size -= sum(map(len, p_excl)) + len(p_excl)

            is_bc = self.__is_biclique((ss, pp))

            # if we include this we get additional size
            if size > 0:
                h = optimizer.add_soft(_z3.Not(is_bc), size)

            # Add back any omitted nodes if used
            for s in s_excl:
                j = s_excl[s]
                # is_bc => ex_s_vars
                h = optimizer.add_soft(
                        _z3.Or(_z3.Not(is_bc), self.ex_s_vars[j]),
                        len(s) + 1
                    )

            for p in p_excl:
                j = p_excl[p]
                # is_bc => ex_p_vars
                h = optimizer.add_soft(
                        _z3.Or(_z3.Not(is_bc), self.ex_p_vars[j]),
                        len(p) + 1
                    )

        return h

    def __has_edge_e(self, e, optimizer):
        """
        :param e:
            A simplerule
        :param optimizer:
            A Z3 Optimize to add any new constraints to
        :returns:
            Variable that is true iff e appears in ith inserted biclique
        """
        return self.__has_edge(e.getSelector(), e.getProperty(), optimizer)

    def __has_edge(self, s, p, optimizer):
        """
        :param s:
            A selector in same format as simpleRule
        :param p:
            A propery in same format as simpleRule
        :param optimizer:
            A Z3 Optimize to add any new constraints to
        :returns:
            A variable that is true iff (s, p) appears as in edge in the new biclique
        """
        if (s, p) in self.__has_edge_memo:
            return self.__has_edge_memo[(s, p)]
        else:
            possiblities = []
            for bc in self.edgebcs[(s, p)]:
                bc_i = self.bidxs[bc]
                s_excls = self.s_excls[bc]
                p_excls = self.p_excls[bc]

                # variable true iff we're in this biclique
                is_bc_v = self.__is_biclique_n(bc_i)

                # make list of ways s,p can be excluded
                lit_list = []
                if s in s_excls:
                    lit_list.append(_z3.Not(self.ex_s_vars[s_excls[s]]))
                if p in p_excls:
                    lit_list.append(_z3.Not(self.ex_p_vars[p_excls[p]]))

                # if can't exclude edge, just knowing it's this biclique is
                # enough
                if len(lit_list) == 0:
                    possiblities.append(is_bc_v)
                else:
                    lit_list.append(is_bc_v)

                    # Create new var for __has_edge
                    bc_has_v = _z3.Bool("bc_" + str(bc_i) + "_has_" +
                                        str(s) + "_" + str(p))

                    # assert bc_has_v <=> is_bc_v & not_excl_s & not_excl_p
                    cnf_v_iff_conj(bc_has_v, lit_list, optimizer, _z3)

                    possiblities.append(bc_has_v)

            # Each edge is in at least one max biclique, so len never 0
            if len(possiblities) == 1:
                self.__has_edge_memo[(s, p)] = possiblities[0]
                return possiblities[0]
            else:
                has_v = _z3.Bool("has_" + str(s) + "_" + str(p))

                # assert has_v <=> possiblities[0] or ... or possiblities[n]
                cnf_v_iff_disj(has_v, possiblities, optimizer, _z3)

                self.__has_edge_memo[(s, p)] = has_v
                return has_v


    def __is_biclique(self, bc):
        """
        :param bc:
            pair (ss, pp) of selectors (from a simpleRule) and properties (from
            a simpleRule) that is a biclique of the CSS
        :returns:
            z3 variable that is true iff the inserted bucket has biclique bc
        """
        return self.__is_biclique_n(self.bidxs[bc])


    def __is_biclique_n(self, n):
        """
        :param n:
            An index in range(self.nbicliques)
        :returns:
            z3 variable that is true iff the inserted bucket has biclique bc
        """
        return self.bvar == n


    def __add_indices_in_bounds_fmla(self, optimizer):
        """Adds formula asserting that the biclique is put into a sensible position
        in the file

        :param optimizer:
            A Z3 Optimize to add constraints to
        """
        optimizer.add(self.idx >= 0)
        optimizer.add(self.idx <= self.clique.num_rules() + 1)


    def __add_count_size(self, optimizer):
        """Adds soft constraints calculating size of file after refactoring and trimming

        :param optimizer:
            A Z3 Optimize to add soft constraints to
        :returns:
            A Z3 handle to the soft constraints if created, else None
        """
        h = None
        for i in range(self.clique.num_rules()):
            h = self.__add_clique_count_size(i, optimizer)

        h2 = self.__add_clique_size(optimizer)

        if h2 is not None:
            return h2
        else:
            return h


    def __add_clique_count_size(self, i, optimizer):
        """Adds soft constraint counting the size of each clique i after the
        refactoring.  Not quite accurate since we don't detect savings from
        emptied bicliques.

        :param i:
            An index in range(num rules in clique)
        :param optimizer:
            A Z3 Optimize to add soft_constraints to
        :returns:
            A Z3 handle to the soft_constraints, else None if none created
        """
        h = None
        (ss, pp) = self.clique.cliques[i]

        # now subtract any nodes we can remove
        for s in ss:
            # can remove if all incident edges appearing here last appear later
            # or in new bucket (if new bucket appears later)
            can_remove = [ self.__has_edge(s, p, optimizer)
                           for p in pp
                           if self.last_index[simpleRule(s, p)] == i ]
            can_remove.append(i < self.idx)

            can_remove_v = _z3.Bool("can_remove_s_" + str(s) + "_from_bucket_" + str(i))

            cnf_v_iff_conj(can_remove_v, can_remove, optimizer, _z3)

            # if edge appears after bucket, or can't remove, cost is len(s) + 1
            # for trailing ,
            h = optimizer.add_soft(can_remove_v, len(s) + 1)

        for p in pp:
            can_remove = [ self.__has_edge(s, p, optimizer)
                           for s in ss
                           if self.last_index[simpleRule(s, p)] == i ]
            can_remove.append(i < self.idx)

            can_remove_v = _z3.Bool("can_remove_p_" + str(p) + "_from_bucket_" + str(i))

            cnf_v_iff_conj(can_remove_v, can_remove, optimizer, _z3)

            h = optimizer.add_soft(can_remove_v, len(p) + 1)

        return h


    def __add_refactor_respects_order(self, optimizer):
        """Adds a formula asserting that the refactoring does not violate the
        edge ordering.

        :param optimizer:
            A Z3 Optimize to add constraints to
        """
        # Find out last index of each edge
        # Assert for each (e1, e2) with e1 in bucket, that last e2 > i or e2 is
        # also in bucket
        for (e1, e2) in self.simple.edgeOrder:
            # has_edge => idx < last_idx or e2 in bucket
            optimizer.add(_z3.Or(_z3.Not(self.__has_edge_e(e1, optimizer)),
                                 self.idx <= self.last_index[e2],
                                 self.__has_edge_e(e2, optimizer)))

        # to respect order we also have to be careful not to use forbidden
        # buckets!
        for i in range(self.clique.num_rules()+1):
            forbidden = self.forbidden[i]
            if len(forbidden) > 0:
                for (ss, pp) in forbidden:
                    if self.__is_possible_biclique((ss, pp)):
                        # idx > j => not forbidden
                        optimizer.add(_z3.Or(self.idx < i,
                                             _z3.Not(self.__is_biclique((ss, pp)))))

    def __is_possible_biclique(self, bc):
        """
        :param bc:
            A biclique (ss, pp)
        :returns:
            True iff bc is an option in self.bicliques
        """
        return bc in self.bidxs


    def __add_exclude_only_in(self, optimizer):
        """Adds to optimizer constraints that say ex_s_vars and ex_p_vars are
        false for all variables that do not have any effect on the selected max
        biclique.

        :param optimizer:
            A Z3 optimizer to add the constraints to
        """
        for (ss, pp) in self.bicliques:
            # is biclique => not ex_s_var (for those out of range)
            for i in range(len(ss), len(self.ex_s_vars), 1):
                optimizer.add(_z3.Or(_z3.Not(self.__is_biclique((ss, pp))),
                                     _z3.Not(self.ex_s_vars[i])))
            # is biclique => not ex_p_var
            for i in range(len(pp), len(self.ex_p_vars), 1):
                optimizer.add(_z3.Or(_z3.Not(self.__is_biclique((ss, pp))),
                                     _z3.Not(self.ex_p_vars[i])))

class _Z3EncoderSimple(object):
    """Encodes the problem of identifying a refactoring as a Z3 formula.
       Uses one boolean var per selector or property that can be in the new rule.
    """
    def __init__(self, clique, simple, partition, num_partitions):
        """
        :param clique:
            The cliqueCSS to optimise
        :param simple:
            A simpleCSS equivalent to the cliqueCSS
        :param partition:
            Search for refactorings in every positions that mod
            num_partitions are = partition
        :param num_partitions:
            See above
        """
        self.clique = clique
        self.simple = simple
        self.partition = partition
        self.num_partitions = num_partitions

        # position to insert biclique
        self.idx = CNFInt("idx", self.clique.num_rules() + 1, _z3)

        # need to know last index of all edges to calculate savings and if edge
        # order respected
        self.last_index = clique.build_last_index_map()

        self.sels = { r1.getSelector() for r1 in self.simple.getEdgeSet() }
        self.props = { r1.getProperty() for r1 in self.simple.getEdgeSet() }

        self.s_vars = { s : _z3.Bool(str(s)) for s in self.sels }
        self.p_vars = { p : _z3.Bool(str(p)) for p in self.props }


    def add_hard_constraints(self, optimizer):
        """Add a formula putting required constraints on get_soft_constraints

        :param optimizer:
            A Z3 Optimizer to add hard constraints to
        """
        self.__add_index_in_bounds_fmla(optimizer)
        self.__add_edges_exist(optimizer)
        self.__add_refactor_respects_order(optimizer)
        if self.num_partitions > 1:
            optimizer.add(self.idx.lsb_with(self.partition))

    def add_soft_constraints(self, optimizer):
        """Add formulas that needs to be maximised to find the best refactoring.
           Relies on get_constraints() also being asserted

        :param optimizer:
            A Z3 Optimize to add soft constraints to
        :return:
            A handle to the soft constraints
        """
        return self.__add_count_size(optimizer)

    def add_final_constraints(self, optimizer):
        """Adds final constraints that should be asserted after all others have been added.

        :param optimizer:
            A Z3 Optimize to add the constraints to
        """
        for c in self.idx.get_variable_constraints():
            optimizer.add(c)

    def _get_index(self, model):
        """
        :param model:
            A Z3 model of the constructed formula
        :returns:
            The index of the refactoring as Integer
        """
        return self.idx.get_value(model)

    def _get_size(self, handle):
        """
        :param handle:
            The Z3 optimisation handle associated to the formula or None
        :returns:
            The size of the CSS after the refactoring associated to handle
            or -1 if handle is None
        """
        if handle is None:
            return -1
        else:
            # TODO: this properly
            return int(str(handle.value()))

    def __add_index_in_bounds_fmla(self, optimizer):
        """Adds formula asserting that the biclique is put into a sensible position
        in the file

        :param optimizer:
            A Z3 Optimize to add constraints to
        """
        optimizer.add(self.idx >= 0)
        optimizer.add(self.idx <= self.clique.num_rules() + 1)


    def __add_count_size(self, optimizer):
        """Adds soft constraints calculating size of file after refactoring and trimming

        :param optimizer:
            A Z3 Optimize to add soft constraints to
        :returns:
            A Z3 handle to the soft constraints if created, else None
        """
        h = None
        for i in range(self.clique.num_rules()):
            h = self.__add_clique_count_size(i, optimizer)

        h2 = self._add_clique_size(optimizer)

        if h2 is not None:
            return h2
        else:
            return h


    def __add_clique_count_size(self, i, optimizer):
        """Adds soft constraint counting the size of each clique i after the
        refactoring.  Not quite accurate since we don't detect savings from
        emptied bicliques.

        :param i:
            An index in range(num rules in clique)
        :param optimizer:
            A Z3 Optimize to add soft_constraints to
        :returns:
            A Z3 handle to the soft_constraints, else None if none created
        """
        h = None
        (ss, pp) = self.clique.cliques[i]

        # now subtract any nodes we can remove
        for s in ss:
            # can remove if all incident edges appearing here last appear later
            # or in new bucket (if new bucket appears later)
            can_remove = _z3.And([ self._has_edge(s, p)
                                   for p in pp
                                   if self.last_index[simpleRule(s, p)] == i ])
            # if edge appears after bucket, or can't remove, cost is len(s) + 1
            # for trailing ,
            h = optimizer.add_soft(_z3.And(i < self.idx, can_remove), len(s) + 1)

        for p in pp:
            can_remove = _z3.And([ self._has_edge(s, p)
                                   for s in ss
                                   if self.last_index[simpleRule(s, p)] == i ])
            h = optimizer.add_soft(_z3.And(i < self.idx, can_remove), len(p) + 1)

        return h

    def __add_edges_exist(self, optimizer):
       """Adds a formula asserting that edges in the refactoring actually exist"""
       for (s, p) in product(self.sels, self.props):
           e = simpleRule(s, p)
           if e not in self.last_index:
               optimizer.add(_z3.Not(self.__has_edge_e(e)))

    def __add_refactor_respects_order(self, optimizer):
        """Adds a formula asserting that the refactoring does not violate the
        edge ordering.

        :param optimizer:
            A Z3 Optimize to add constraints to
        """
        # Find out last index of each edge
        # Assert for each (e1, e2) with e1 in bucket, that last e2 > i
        for (e1, e2) in self.simple.edgeOrder:
            optimizer.add(_z3.Or(_z3.Not(self.__has_edge_e(e1)),
                                  self.idx < self.last_index[e2]))

    def __has_edge_e(self, e):
        """
        :param e:
            A simplerule
        :returns:
            Formula asserting e appears in inserted biclique
        """
        return self._has_edge(e.getSelector(),
                              e.getProperty())

    def get_refactoring(self, model, handle):
        """Returns the refactoring corresponding to the model found by Z3

        :param model:
            The model returned by Z3 .model()
        :param handle:
            A Z3 handle to the soft constraints or None if not available (in
            which case the returned refactoring will not estimate size of
            refactored file)
        """

        ss_res = set()
        pp_res = []

        for (s, v) in self.s_vars.items():
            if _z3.is_true(model[v]):
                ss_res.add(s)

        for (p, v) in self.p_vars.items():
            if _z3.is_true(model[v]):
                pp_res.append(p)

        idx = self._get_index(model)
        size = self._get_size(handle)

        return Refactoring([(idx, ss_res, pp_res)], size)

    def _add_clique_size(self, optimizer):
        """Adds soft constraints to count weight of new clique

        :param optimizer:
            The Z3 Optimize to add soft constraints to
        :returns:
            A Z3 handle to the soft constraints if any added, else None
        """
        # There is also a cost of 2 for { and }
        # But a saving of two since the +1 is for separating , and ; overcounts
        # by 2 (since only needed as separators)
        h = None
        for (s, v) in self.s_vars.items():
            h = optimizer.add_soft(_z3.Not(v), len(s) + 1)
        for (p, v) in self.p_vars.items():
            h = optimizer.add_soft(_z3.Not(v), len(p) + 1)
        return h


    def _has_edge(self, s, p):
        """
        :param s"
            A selector from a simpleRule
        :param p:
            A property from a simpleRule
        :returns:
            A z3 formula asserting (s, p) appears in inserted biclique
        """
        return _z3.And([self.s_vars[s], self.p_vars[p]])

