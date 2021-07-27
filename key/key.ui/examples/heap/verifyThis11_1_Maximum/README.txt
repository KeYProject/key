example.name = 1 - Finding the Maximum in an Array
example.path = Benchmarks/VerifyThis2011
example.additionalFile.1 = src/Maximum.java

Time:60 minutes

Given:A non-empty integer array a

Challenge:Verify that the index returned by the method max() points to
an element maximal in the array.

Motivation:This challenge is an instance of Kaldewaij’s Search by
Elimination [1], where an element witha given property is located by
eliminating elements that do not have that property. The challenge was
selected as it involves a relatively simple but interesting invariant,
expressing that the maximal element is in the remaining search space,
rather than maintaining the maximal element found so far.
