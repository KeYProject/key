example.name = Quicksort
example.file = project.key
example.additionalFile.1 = Quicksort.java
example.path = Algorithms

This example formalizes and verifies the wellknown quicksort
algorithm for int-arrays algorithm.  It shows that the array
is sorted in  the end and that it contains  a permutation of
the original input.

The   proofs   for   the  main   method   sort(int[])   runs
automatically   while   the   other  two   methods   require
interaction.  You   can  load   the  files   "sort.key"  and
"split.key"  from the  example's  directory  to execute  the
according proof scripts.

The permutation property requires some interaction: The idea
is that the only actual modification on the array are swaps
within the "split" method. The sort method body contains
three method invocations which each maintain the permutation
property. By a repeated appeal to the transitivity of the
permutation property, the entire algorithm can be proved to
only permute the array.

To establish  monotonicity, the key  is to specify  that the
currently  handled block  contains  only  numbers which  are
between   the    two   pivot   values    array[from-1]   and
array[to]. The first  and last block are exempt  from one of
these  conditions  since  they have  only  one  neighbouring
block.

The  example has  been  added  to show  the  power of  proof
scripts.
  Mattias Ulbrich, 2015
