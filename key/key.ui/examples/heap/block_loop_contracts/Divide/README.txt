example.name = Divide and Conquer with Block Contracts
example.path = Dynamic Frames/Block & Loop Contracts
example.additionalFile.1 = src/DualPivotQuicksort_sort_methods.java
example.additionalFile.2 = src/DualPivotQuicksort_sort_blocks.java

"DualPivotQuicksort_sort_methods.java" contains a method "prepare_indices", which is divided into two sub-methods, "calcE" and "eInsertionSort", for easier verification.

"DualPivotQuicksort_sort_methods.java" shows that the same can be achieved by dividing "prepare_indices" into two blocks and applying the rule "External Block Contract". The second block (which corresponds to "eInsertionSort") contains blocks itself. These can only be proven with the rule "Internal Block Contract". See the example "Internal and External Block Contracts" for why this is.

"DualPivotQuicksort_sort_methods.java" is taken from:
    Bernhard Beckert, Jonas Schiffl, Peter H. Schmitt, and Mattias Ulbrich. Proving JDK’s dual pivot quicksort correct. In 9th Working Conference on Verified Software: Theories, Tools, and Experiments (VSTTE 2017), July 2017.


2018, Florian Lanzinger