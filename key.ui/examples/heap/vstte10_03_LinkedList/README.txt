example.name = 3 - Find in Linked List
example.path = Benchmarks/VSComp 10
example.additionalFile.1 = src/Node.java

The third challenge from the Verified Software Competition (VSComp) at VSTTE'10, organised by Peter Mueller and Natarajan Shankar: 

Given a linked list representation of a list of integers, find the index of the first element that is equal to 0.

This solution is inspired by the Dafny solution submitted by Rustan Leino. It uses a recursively defined invariant instead of a reachability predicate for dealing with the recursive nature of the linked list datastructure. A "sequence" abstract data type has been implemented in KeYHeap for this example, as well as Dafny's "limited" trick for limiting the automatic unfolding of recursive represents clauses to one level.

All three proof obligations can be verified without user interaction.
