example.name = 5 - Red-Black Trees
example.path = Benchmarks/VACID-0
example.additionalFile.1 = src/vacid0/redblacktree/RedBlackTree.java
example.additionalFile.2 = src/vacid0/redblacktree/Harness.java
example.additionalFile.3 = src/vacid0/redblacktree/Node.java
example.additionalFile.4 = src/vacid0/redblacktree/AbstractMap.java


README on VACID-0: Red-black trees
Author: Daniel Bruns <bruns@kit.edu>
Last change date: Aug 12, 2011

0. Introduction
Red-black trees are the final item in Leino and Moskal's VACID-0 benchmark [1]. The specifications here are given in JML*, i.e., an extension to JML to support dynamic frames and sequence ADTs. Theoretical background can be found in Benjamin Weiß' thesis [2]. All proofs are done using KeY 1.7 (the development branch to become 2.0); it does not work with KeY <= 1.6 or any other future versions than the 2.0 up-branch. In any case, you should use the most recent development version ( >= August 1, 2011).

1. Verifying the harness
The test harness was given in [1] and is meant to be verified modularily. This means that no information on the implementation of the AbstractMap interface is to be used. There is no postcondition given for method redBlackTestHarness() which means that it is to show that it terminates without raising an Error. So, starting KeY with the assertion option is essential (this is the default). Since the proof mostly consists of application of contracts and branches frequently, it cannot (yet) be done automatically. It is useful to set the maximum rule applications to around 20 and method treatment to none (there is usually need for user interaction after the application of a contract). Due to the many method calls the proof methodology repeats once and again, thus it suffices to give a short sketch of the proof.

Expand the harness method and push auto-button. Apply contract to replace(). The "Post" branch is the interesting one; all other can be closed automatically. Push button and apply contract to replace(). First look at the "Pre" branch; here we need to show that the precondition on object b holds after the operation on object a -- the typical aliasing and framing problem. In the succedent, apply One Step Simplication and split the conjunction; two branches close automatically. Click on <inv> in the succedent and apply Dependency Contract. The first branch is trivial again; in the second one, we need to show disjointness of the dynamic frames of a and b. Split the conjunction and close the 5 trivial branches. Disjointness of frames is given through the invariant of AbstractMap, however. Select "Partial inv axiom..." on a.<inv> and instantiate the resulting quanfied formula with b. Push the button and the "Pre" branch is closed. Repeat until we reach the lookup() method.

Apply contract on lookup(). The "Pre" branch needs to be handled as before. In the "Post" branch, we now have the formula "seqGet(contents(...),1) = result" in the antecedent. The difficult thing is that contents is to be valuated in heap heapAfter_lookup, but the interesting information we have is on heapAfter_replace. Therefore, we need to apply dependency contracts and equality insertions several times. Start by applying the dependency contract on contents against heapAfter_replace_2 (only this choice). The second branch is handled similar to above. On the first branch, apply the newly gained equality formula on the "seqGet" formula. Repeat until we reache heapAfter_replace. Note that the dependency contract may only be used against the "preceeding" heap since every second one does change the value of contents.

We now have a seqGet term which is only evaluated in the original heap. Apply sequence rewriting rules by hand until we have "1 = result". Apply it to the program and continue.

n. Bibliography
[1] K. Rustan M. Leino and Michał Moskal. VACID-0: Verification of Ample Correctness of Invariants of Data-structures, Edition 0. In Tools and Experiments workshop at VSTTE 2010, Edinburgh, UK, 2010.
[2] Benjamin Weiß. Deductive Verification of Object-oriented Software: Dynamic Frames, Dynamic Logic and Predicate Abstraction. PhD thesis, Karlsruhe Institute of Technology, 2011.
