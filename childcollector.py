"""ChildCollector

Used to collect subprocesses created by multiprocessing.Process
instances used for --num-threads.  Also provides locks to ensure that
the tool when wanting to stop all children does not have to race to kill
a thread before it creates any children."""

import multiprocessing

class ChildCollectorException(Exception):
    pass


class ChildCollector:

    def __init__(self):
        self.__child_list = multiprocessing.Queue()
        self.__create_child_lock = multiprocessing.Queue()
        self.__create_child_lock.put(None)

    def get_create_child_lock(self):
        """Before creating any children, get this lock and then add the
        child using add_new_child()"""
        self.__create_child_lock.get()

    def add_new_child(self, child):
        """Register the creation of a new child with a .terminate or
        method

        :param child:
            a child process that can be stopped with .terminate
        """
        self.__child_list.put(child)

    def release_create_child_lock(self):
        """After creating and registering the child, release the lock"""
        self.__create_child_lock.put(None)

    def terminate_children(self):
        """Make sure all children have terminated: terminate using
        .terminate.  Acquires get_create_child_lock before doing the
        termination."""
        self.get_create_child_lock()
        while not self.__child_list.empty():
            child = self.__child_list.get()
            if hasattr(child, 'terminate'):
                try:
                    child.terminate()
                except OSError:
                    if child.poll() is None:
                        raise ChildCollectorException("Failed to kill child!")
            else:
                raise ChildCollectorException("Child has no terminate!")
        self.release_create_child_lock()
