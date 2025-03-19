example.name = Permuted Sum
example.path = Algorithms
example.file = perm.key
example.additionalFile.1 = src/Perm.java
# Please ensure that the following file is included into the group reload_examples within automaticJAVADL.txt.
example.proofFile = perm.proof

Compute a sum of integers through the order given by an iterator. The exact order is not known, except for the fact that each element is selected exactly once.

For simplicity, this implementation uses an array instead of a (generic) collection type.

The proof does not go through automatically. Apply the Full Autopilot macro (make sure that the strategy option "Class Axiom Rule" is set to "Delayed"). On the remaining goal, apply the "equal_bsum_perm" rule. Unfold the invariant on the LHS. You need to prove that the two "seqPerm" predicates on both side are talking about the same things. This requires some more well-chosen cuts (see the attached proof).
