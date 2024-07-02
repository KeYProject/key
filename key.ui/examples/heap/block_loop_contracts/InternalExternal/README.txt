example.name = Internal and External Block Contracts
example.path = Dynamic Frames/Block & Loop Contracts
example.additionalFile.1 = src/DualPivotQuicksort_sort_internal.java
example.additionalFile.2 = src/DualPivotQuicksort_sort_external.java

This example demonstrates the difference between the rules "External Block Contract" and "Internal Block Contract".

The method in "DualPivotQuicksort_sort_internal.java" is only provable with the internal rule because the block contracts do not have any preconditions.

"DualPivotQuicksort_sort_external.java" contains the same method, but with additional preconditions on the block contracts, so that it becomes provable with the external rule.

"DualPivotQuicksort_sort_internal.java" and the proof file for it are taken from:
    Bernhard Beckert, Jonas Schiffl, Peter H. Schmitt, and Mattias Ulbrich. Proving JDK’s dual pivot quicksort correct. In 9th Working Conference on Verified Software: Theories, Tools, and Experiments (VSTTE 2017), July 2017.
    

2018, Florian Lanzinger