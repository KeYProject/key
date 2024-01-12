example.name = 2 - Invert Array
example.path = Benchmarks/VSComp 10
example.additionalFile.1 = src/Invert.java

The second challenge from the Verified Software Competition (VSComp) at VSTTE'10, organised by Peter Mueller and Natarajan Shankar: 

Invert an injective array A on N elements in the subrange from 0 to N − 1, i.e., the output array B must be such that B[A[i]] = i for 0 <= i < N.

This is the solution created by the KeY team during the competition using regular KeY 1.5, slightly adapted for KeYHeap.

The single proof obligation is verifiable interactively: Switch off quantifier instantiation to prevent matching loop; use Z3; instantiate double quantifier; use Z3.   
