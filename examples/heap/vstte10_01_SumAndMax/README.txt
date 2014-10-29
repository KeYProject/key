example.name = 1 - Sum and Max
example.path = Benchmarks/VSComp 10
example.additionalFile.1 = src/SumAndMax.java

The first challenge from the Verified Software Competition (VSComp) at VSTTE'10, organised by Peter Mueller and Natarajan Shankar: 

Given an N-element array of natural numbers, write a program to compute the sum and the maximum of the elements in the array.

This is the solution created by the KeY team during the competition using regular KeY 1.5, slightly adapted for KeYHeap.

The single proof obligation is verifiable without user interaction (but note that "Arithmetic Treatment" is switched to "Model Search" in the strategy configuration).
