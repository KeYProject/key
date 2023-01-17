example.name = List with Observers
example.path = Dynamic Frames
example.additionalFile.1 = src/List.java
example.additionalFile.2 = src/ArrayList.java
example.additionalFile.3 = src/LinkedList.java
example.additionalFile.4 = src/Node.java
example.additionalFile.5 = src/ListIterator.java
example.additionalFile.6 = src/Client.java
example.additionalFile.7 = src/MySet.java


A list interface with iterators, an array list and a linked list implementation, a set class built on top of the list, and another client that uses the list. 

Note that unlike the array list, the *linked* list is experimental and unfinished. Another (perhaps more promising) approach to dealing with linked lists can be found in the "vstte10_03_LinkedList" and "vstte10_05_Queue" examples. 

Interactive proofs:
- ArrayList::contains (obvious quantifier instantiation)
- ArrayList::remove (manual quantifier instantiations; auto instantiation seems to run into a matching loop)
- Client::listContainsMe (obvious quantifier instantiations)
- LinkedList::footprint (apply reachDependenciesChangeHeapAtLocs)
- LinkedList::\inv (apply reachDependenciesChangeHeapAtLocs)
- MySet's second constructor (obvious quantifier instantiations)
- MySet::add (relatively obvious quantifier instantiations [self.list.size()])
- MySet::contains (obvious quantifier instantiation)
- MySet::remove (manual case split before applying method contract)
- MySet::\inv (obvious quantifier instantiations)

Not yet verified:
- LinkedList::add
- LinkedList::contains
- LinkedList: some depends clauses
- MySet::addAll
