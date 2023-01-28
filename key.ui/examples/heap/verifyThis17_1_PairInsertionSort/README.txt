example.name = Pair Insertion Sort
example.path = Benchmarks/VerifyThis2017
example.additionalFile.1 = src/PairInsertionSort.java
# Please ensure that the following file is included into the group reload_examples within automaticJAVADL.txt.
example.proofFile = sort.proof.gz

This is the first challenge from the VerifyThis competition
@ ETAPS 2017 organized by M. Huisman, R. Monahan, W. Mostowski,
P. Müller, and M. Ulbrich.

Although it is an algorithm with O(n²) complexity, this sorting
algorithm is used in modern library implementations. When dealing
with smaller numbers of elements, insertion sorts performs better
than, e.g., quicksort due to a lower overhead. It can be imple-
mented more efficiently if the array traversal (and rearrangement)
is not repeated for every element individually. This version of
Pair Insertion Sort handles two elements at once and is used by
Oracle's implementation of the Java Development Kit (JDK) for
sorting primitive values and small problem instances of less than
47 elements. In the code snippet, a is the array to be sorted, and
the integer variables left and right are valid indices into a that
set the range to be sorted.

The enclosed proof and specification verify that the given array
is sorted at the end of the method. The example produces a medium
to large size proof in KeY which requires a significant amount of
user assistance.
