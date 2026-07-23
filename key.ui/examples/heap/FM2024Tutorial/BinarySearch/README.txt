example.name = Binary Search
example.path = FM 2024 Tutorial
example.additionalFile.1 = src/BinSearch.java

The binary search examples from the paper "The Java verification tool KeY: A tutorial" presented as the Formal Methods Symposium 2024 in Milan.

@author Bernhard Beckert, Richard Bubel, Daniel Drodt, Reiner Hähnle, Florian Lanzinger, Wolfram Pfeifer, Mattias Ulbrich, Alexander Weigl

Binary search returns the index of a given element in a sorted array if it exists.

The example contains two implementations of binary search: recursive and iterative. The former return -1 if the element is not found; the latter throws an exception in that case. Both example close without user interaction.