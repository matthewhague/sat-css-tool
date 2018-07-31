"""Attempts css-analyser style refactoring minimisation by using a constraint
solver to find a biclique that can be added to the CSS file, followed by a
safe_trim (removing newly redundant edges), to reduce the size of the file.
This is repeated until no more refactorings can be found.

Note: operates on a cliqueCSS object with a given simpleCSS for edgeOrder &c.

Note: Two implementations are available.  See _Z3EncoderSimple and
      _Z3EncoderBiclique.  The latter seems to work best.
"""

import copy
from timeit import default_timer
from math import ceil, log
import operator
from enum import Enum
import random
import multiprocessing
import Queue
import os
import shutil

import simplecssbuilder
from refactoring import *
from all_in_deduct_refactor import all_in_find_refactoring, RefactoringType
from safetrim import safe_trim
from childcollector import ChildCollector

INIT_ANNEAL_PROB = 0.5
ANNEAL_DELTA = 0.001

WAIT_TIME_FACTOR = 0.1

# for heuristically guessing how many partitions and threads to use,
# assign about this many nodes to a partition
NODES_PER_PART = 750

class AnnealType(Enum):
    """No annealing"""
    none = 0
    """Allow non-optimal refactorings as long as file size shrinks"""
    good = 1
    """Allow any refactorings when annealing"""
    any = 2


def refactor(css, timebound = 60000):
    """
    :param css:
        A CSSFile object
    :param timebound:
        A timebound on calls to Z3, default 60s (currently unsupported)
    :returns:
        A refactored version of css that is smaller, as a cliqueCSS
    """
    print "Building cliqueCSS..."
    (simple, clique) = simplecssbuilder.fromcssfile(css, make_clique_css = True)

    from main import get_output_simple, get_dont_refactor
    if get_output_simple():
        print "Simple CSS:"
        print str(simple)
    if get_dont_refactor():
        return clique

    start_t = default_timer()

    #Choose one of the following three strategies
    _clique_refactor(clique, simple, timebound) #Original
    #clique_refactor_double(clique, simple, timebound) #Double
    #clique_refactor_combined(clique, simple, timebound) #Combined

    end_t = default_timer()

    print "Time to refactor:", (end_t - start_t), "s"

    print "Checking result is correct."
    assert clique.equivalent(simple), \
            "deduct_refactor did not construct an equivalent CSS"

    return clique


class RefactorThread:
    """A thread running a part of a refactoring search"""

    def __init__(self, thread_no, num_threads, num_parts):
        """
        :param thread_no:
            The thread number (Integer) ie 0th, 1st, 2nd,...
        :param num_threads:
            The total number of threads being used
        :param num_parts:
            The number of partitions to be searched by each thread
        """
        self.__thread_no = thread_no
        self.__num_threads = num_threads
        self.__num_parts = num_parts

    def find_refactoring(self,
                         clique, simple,
                         iter_no,
                         timebound,
                         ref_type,
                         result_q = None,
                         child_collector = None):
        """
        :param clique:
            A cliqueCSS to find a refactoring for
        :param simple:
            A simpleCSS equivalent to cliqueCSS
        :param iter_no:
            The number of iterations so far (thread starts searching its
            partition space at this number modulo number of partitions)
        :param ref_type:
            which RefactoringType to use
        :param timebound:
            timeout
        :param result_q:
            A multiprocessing.Queue to write refactoring to when found.
            If None, then does not add result to queue
        :param child_collector:
            A ChildCollector used to track all instances of z3 created by
            child threads
        :returns:
            A Refactoring or None if none found
        """
        refactoring = None
        num_tries = 0
        size = clique.size()

        print "clique has", clique.num_rules(), "rules"
        print "clique has", clique.num_nodes(), "nodes"

        total_parts = self.__num_threads * self.__num_parts
        base_part = self.__thread_no * self.__num_parts

        # Try at most num_parts number of times to find a
        # refactoring.  Do not accept a refactoring that will
        # increase size if best/good refactoring required
        while ((num_tries < self.__num_parts) and
               ((refactoring is None) or
                (ref_type != RefactoringType.any and
                 refactoring.size >= size))):

            part_no = base_part + (iter_no % self.__num_parts)

            print "Thread", self.__thread_no, "iteration", iter_no, \
                  "trying partition", part_no, "of", total_parts

            refactoring = self.__find_refactoring_part(clique, simple,
                                                       timebound,
                                                       ref_type,
                                                       part_no, total_parts)
            iter_no += 1
            num_tries += 1

        if result_q is not None:
            result_q.put(refactoring)

        return refactoring

    def __find_refactoring_part(self,
                                clique, simple,
                                timebound,
                                ref_type,
                                partition, num_partitions,
                                child_collector = None):
        """Find a refactoring to apply to clique within a given partition

        :param clique:
            A cliqueCSS
        :param simple:
            A simpleCSS equivalent to the cliqueCSS
        :param timebound:
            A bound on calls to Z3
        :param ref_type:
            The type of refactoring from all_in_deduct_refactor RefactoringType
            (only works with all_in_deduct_refactor)
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
        start_t = default_timer()
        refactoring = None
        refactoring = all_in_find_refactoring(clique, simple,
                                              timebound,
                                              ref_type,
                                              partition, num_partitions,
                                              child_collector)
        end_t = default_timer()
        print "Finding refactoring took", (end_t - start_t), "s"
        return refactoring







def _clique_refactor(clique, simple, timebound = 60000):
    """
    Refactors the given cliqueCSS in place in an attempt to reduce size.

    :param clique:
        A cliqueCSS to refactor
    :param simple:
        A simpleCSS object equivalent to cliqueCSS
    :param timebound:
        A timebound on calls to Z3, default being 60s (currently unsupported)
    """
    total_start_t = default_timer()
    num_iters = 0

    from main import get_intermediates_directory
    res_dir = get_intermediates_directory()
    _setup_results_directory(res_dir)

    original_size = clique.size()

    _write_result_clique(clique, simple, "original", res_dir, original_size, total_start_t)

    # Initial trim since inherent redundancy could confuse first iteration
    # of refactoring
    print "Before initial trim has size", original_size, "bytes"
    trim_file(clique)

    _write_result_clique(clique, simple, num_iters, res_dir, original_size, total_start_t)

    random.seed()
    from main import get_anneal
    anneal_type = get_anneal()

    anneal_prob = INIT_ANNEAL_PROB if anneal_type != AnnealType.none else 1.0

    num_threads, num_parts = _calc_num_threads_parts(clique)
    print "Using", num_threads, "threads and", num_parts, "partitions per thread"

    threads = [ RefactorThread(thread_no, num_threads, num_parts)
                for thread_no in xrange(num_threads) ]


    # repeat until we can't find a refactoring
    while True:
        num_iters += 1
        size = clique.size()

        print "Searching for refactoring..."
        print "Beginning with size", size, "bytes"

        ref_type = RefactoringType.best
        if random.random() > anneal_prob:
            print "Allowing any solution"
            if anneal_type == AnnealType.good:
                ref_type = RefactoringType.good
            else:
                ref_type = RefactoringType.any
            anneal_prob += ANNEAL_DELTA

        refactoring = None

        if num_threads == 1:
            refactoring = threads[0].find_refactoring(clique, simple,
                                                      num_iters,
                                                      timebound,
                                                      ref_type)
        else:
            q = multiprocessing.Queue()
            child_collector = ChildCollector()

            real_threads = [ multiprocessing.Process(
                                target=threads[i].find_refactoring,
                                args=(clique, simple,
                                      num_iters,
                                      timebound,
                                      ref_type,
                                      q, child_collector))
                             for i in xrange(num_threads) ]

            for i in xrange(num_threads):
                real_threads[i].start()

            start_t = default_timer()
            refactoring = None
            num_possibilities = num_threads

            while refactoring is None and num_possibilities > 0:
                refactoring = q.get()
                num_possibilities -= 1

            end_t = default_timer()

            if refactoring is not None:
                wait_time = WAIT_TIME_FACTOR * (end_t - start_t)
                print "Waiting up to", wait_time, "s for better refactoring."
                refactoring = _wait_for_better_refactoring(q,
                                                           refactoring,
                                                           wait_time,
                                                           num_possibilities)

            for i in xrange(num_threads):
                real_threads[i].terminate()
            for i in xrange(num_threads):
                real_threads[i].join()
            child_collector.terminate_children()

        if refactoring is None:
            print "No refactoring found"
            break

        # lastfile = open("lastone.css", "w")
        # lastfile.write(str(clique))
        # lastfile.close()

        # If refactoring didn't save anything, give up
        if ref_type == RefactoringType.best:
            if refactoring.size < 0:
                print "WARNING: refactoring estimated size is < 0.  Without a proper estimate of size we may make the file larger."
            elif refactoring.size >= size:
                print "Estimated saving is <= 0, not applying refactoring and assuming no further refactoring is possible."
                break

        print "Applying refactoring: " + str(refactoring)

        refactoring.apply(clique)

        assert clique.equivalent(simple), "Refactoring produced an inequivalent CSS."

        _write_result_clique(clique,
                             simple,
                             num_iters,
                             res_dir,
                             original_size,
                             total_start_t)

        new_size = clique.size()
        pc_saving = operator.truediv((original_size - new_size), original_size) * 100

        print "Removed", (size - new_size), "bytes"
        print "New size", new_size, \
              "bytes saves", (original_size - new_size), \
              "(", pc_saving, "%)"

        # If refactoring didn't save anything, give up
        if ref_type == RefactoringType.best and new_size >= size:
            break;

    new_size = clique.size()
    print "Refactoring complete, new size is", new_size, "bytes"
    pc_saving = operator.truediv((original_size - new_size), original_size) * 100
    print "Saved ", pc_saving, "%"

def _calc_num_threads_parts(clique):
    """Implements a rough heuristic to guess how many threads and
    partitions to use, taking into account what was suggested on the
    command line.  Tries to allocate NODES_PER_PART nodes per partition.

    :param clique:
        A cliqueCSS
    :returns:
        pair of ints (threads, parts)
        where threads is the number of threads to use
        and parts is the number of parts per thread
    """
    from main import get_num_threads, get_num_parts
    num_threads = get_num_threads()
    num_parts = get_num_parts()

    if num_threads is not None and num_parts is not None:
        return (num_threads, num_parts)

    num_nodes = clique.num_nodes()

    if num_threads is not None:
        nodes_per_thread = num_nodes / float(num_threads)
        num_parts = ceil(nodes_per_thread / float(NODES_PER_PART))
        return (num_threads, int(num_parts))

    num_cpus = multiprocessing.cpu_count()

    if num_parts is not None:
        nodes_per_part = num_nodes / float(num_parts)
        ideal_threads = ceil(nodes_per_part / float(NODES_PER_PART))
        num_threads = min(ideal_threads, num_cpus)
        return (int(num_threads), num_parts)

    # if it's all up to us...
    if num_nodes <= 2 * NODES_PER_PART:
        return (1, int(ceil(num_nodes / float(NODES_PER_PART))))
    elif num_nodes <= num_cpus * NODES_PER_PART:
        return (int(ceil(num_nodes / float(NODES_PER_PART))), 1)
    else:
        nodes_per_cpu = num_nodes / float(num_cpus)
        num_parts = ceil(nodes_per_cpu / float(NODES_PER_PART))
        return (num_cpus, int(num_parts))

def _wait_for_better_refactoring(queue,
                                 best_refactoring,
                                 timeout,
                                 possiblities):

    """
    :param queue:
        Queue from which to .get() Refactoring objects
    :param best_refactoring:
        The best refactoring found so far
    :param timeout:
        How long to wait before giving up
    :param possiblities:
        The number of new refactorings that might be added to queue
    :returns:
        The Refactoring that results in the smallest file size from
        best_refactoring and any refactorings taken from queue, within the
        timeout.
    """
    try:
        timeleft = timeout

        while timeleft > 0 and possiblities > 0:
            start_t = default_timer()
            new_refactoring = queue.get(True, timeleft)
            end_t = default_timer()

            possiblities -= 1
            timeleft -= (end_t - start_t)

            if new_refactoring is not None:
                if new_refactoring.size < best_refactoring.size:
                    best_refactoring = new_refactoring

        return best_refactoring
    except Queue.Empty:
        pass

    return best_refactoring


def _write_result_clique(clique, simple, ident, res_dir, original_size, start_t):
    """If res_dir is not None, records an intermediate result in the given results directory.

    :param clique:
        The cliqueCSS to write
    :param simple:
        A simpleCSS equivalent to the cliqueCSS
    :param ident:
        something to identify this result (calls str() on it)
    :param res_dir:
        the path of an existing directory to write to
    :param original_size:
        the size of the original clique
    :param start_t:
        the time the analysis started (for timings table)
    """
    if res_dir is None:
        return

    clique_f = open(res_dir + os.sep + "result" + str(ident) + ".css", "w")
    clique.write_compact(clique_f)
    clique_f.close()

    table_f = open(res_dir + os.sep + "timings.txt", "a")
    table_f.write("result")
    table_f.write(str(ident))
    table_f.write(", ")
    table_f.write(str(default_timer() - start_t))
    table_f.write(", ")

    size = clique.size()

    table_f.write(str(size))
    table_f.write(", ")
    table_f.write(str(original_size - size))
    table_f.write(", ")
    table_f.write(str(100 * float(original_size - size)/original_size))
    table_f.write("%\n")
    table_f.close()

def _setup_results_directory(res_dir):
    """Sets up the results directory (creates and clears).  Does nothing if
    res_dir is None.

    :param res_dir:
        The directory (string)
    """
    if res_dir is None:
        return

    if os.path.isdir(res_dir):
        if os.listdir(res_dir) != []:
            shutil.rmtree(res_dir)

    if res_dir is not None:
        os.makedirs(res_dir)


