example.name = State Merging
example.path = Getting Started
example.additionalFile.1 = Gcd.java
example.additionalFile.2 = A.java

State merging is a technique to mitigate the path explosion problem of symbolic execution. You can merge together multiple branches in a proof tree that share the same program counter, i.e. the same remaining program to execute (and also the same post condition).

The recommended way for state merging is through the usage of "merge point statements", special specification elements that can be put into the Java source code. The class Gcd has a method "gcd(int, int)" containing two such merge point statements, one for a non-parametric if-then-else method, and the other one for predicate abstraction-based state merging. In the predicate abstraction case, JML is used for the definition of the predicates. As with loop invariants and method contracts, you can use "\old" to refer to the state at the beginning of the method execution.

Still, states can be merged interactively while doing the proof; in this case, you have to select a (top-level) sequent formula in one branch and choose "Merge Rule" as the rule to apply. For this to work, the update of the selected formula has to be simplified, i.e. there is only one update application before the modality. Furthermore, there has to be another sequent formula in a different proof goal which shares the same program and post condition.

The example A.java demonstrates how program variables are renamed in the course of state merging, if there is a name clash: In the method m(), two functions f() and g() are called in distinct branches of an if statement, resulting in variables "result_0" and "exc_0" being created in the branches. Those variables have the same name, but different types (int / Object) and indeed represent different variables. Therefore, after the merge you will find variables "result_0_0" and "result_0_1" (or with different suffixes) representing "result_0" for the respective branches of the if.

For background information on state merging, consult the paper "A General Lattice Model for Merging Symbolic Execution Branches" by Scheurer et al. (2016).