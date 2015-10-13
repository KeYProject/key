example.name = Dancing Links
example.path = Benchmarks/VerifyThis2015
example.additionalFile.1 = src/DoubleLinkedList.java
example.proofFile = doUndo.proof

This is the third challenge from the VerifyThis competition @ ETAPS 2015 organized by M. Huisman, V. Klebanov, and R. Monahan.

Dancing links is a technique introduced in 1979 by Hitotumatu and Noshita and later popularized by Knuth. The technique can be used to efficiently implement a search for all solutions of the exact cover
problem, which in its turn can be used to solve Tiling, Sudoku, N-Queens, and other problems.

The technique works as follows:

Suppose x points to a node of a doubly linked list; let L[x] and R[x] point to the predecessor and successor of that node. Then the operations

L[R[x]] := L[x];
R[L[x]] := R[x];

remove x from the list. The subsequent operations

L[R[x]] := x;
R[L[x]] := x;

will put x back into the list again.

This implementation works with a dedicated head element in order to distinguish the empty list and to simplify the implementation of an explicit construction method. The method 'doUndo(Node x, int k)' executes the description given above.
