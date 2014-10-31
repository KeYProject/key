example.name = Saddleback Search
example.file = Saddleback_search.key
example.additionalFile.1 = Saddleback.java
example.additionalFile.2 = saddle.dfy
example.path = Algorithms

This has been proposed by an exercise by Rustan Leino during the
Marktoberdorf Summer School in 2011.

Given a 2-dimensional array where the values along any row or any
column are non-decreasing, and given a value "s" in the array, find
an index "x,y" such that s == array[x,y].

The runtime had to be linear in the array dimension, i.e. O(max(n,m))
for an array of dimension n*m.

The solution is to start in a corner with one index x set to 0 and the
other y set to maximum. If the value at the current position is larger
then the required value, increase x; if it less, decrease y. Return if
the value has been found.

This directory contains the solution in Dafny (saddle.dfy) and in
Java+JML (Saddleback.java).

The Dafny verifier takes ~ 5s to verify it. (Source attached for
comparison)

If the quantifiers in the sorting preconditions are applied in the right
order, the proof goes through automatically in 21662 nodes on 145 
branches.
