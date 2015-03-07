example.name = Remove Duplicates
example.path = Getting Started
example.additionalFile.1 = RemoveDup.unspecified
example.additionalFile.2 = RemoveDup.java

This is a simple excercise for JML and KeY.

@author Mattias Ulbrich

The specification for removeDup was part of a KIT Formal Systems exam
in Feb 2014. It read:

  Consider the class RemoveDups as implemented in
  RemoveDup.unspecified. The method removeDup removes duplicates from
  a list of numbers. It receives an int-array a and returns a freshly
  created array containing the same values as a, but every value at
  most once. It is ensured that the method does not modify the entries
  of a.

  Give a JML postcondition for the method removeDup saying that the
  result array is at most as long as a.

  Give a JML postcondition for removeDup saying that the result array
  has no duplicates.

  Give a JML postcondition for removeDup saying that every value
  occurring in a also occurs in the result array.

The example contains the solution and specification for all helper
methods.

