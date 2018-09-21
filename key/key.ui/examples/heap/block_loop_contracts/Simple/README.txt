example.name = Simple Examples
example.path = Dynamic Frames/Block & Loop Contracts
example.additionalFile.1 = src/BlockContractExamples.java
example.additionalFile.2 = src/LoopContractExamples.java

This example contains some simple examples for block and loop contracts.

The method "BlockContractExamples.sum" is taken (in a slightly adapted form) from:
    Simon Wacker. Blockverträge. Studienarbeit, Karlsruher Institut für Technologie, October 2012.

The methods in "LoopContractExamples" are based on an example found in:
    Thomas Tuerk. Local reasoning about while-loops. In In International Conference on Verified Software: Theories, Tools and Experiments - Theory Workshop (VS-Theory).

"BlockContractExamplesWithoutPreconditions" is same as "BlockContractExamples" but with all preconditions removed from the block contracts. Thus, the proof obligations in this class can only be proven using the rule "Internal Block Contract".

2018, Florian Lanzinger