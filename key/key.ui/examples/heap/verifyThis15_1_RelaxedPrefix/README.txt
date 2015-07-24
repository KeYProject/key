example.name = Relaxed Prefix
example.path = Benchmarks/VerifyThis2015
example.additionalFile.1 = src/Relaxed.java
example.proofFile = relax.proof

This is the first challenge from the VerifyThis competition @ ETAPS 2015 organized by M. Huisman, V. Klebanov, and R. Monahan.

A 'relaxed prefix' of an array _a_ is an array _pat_ such that, after deleting at most one element from _pat_, the remaining array is a prefix of _a_. 

The implementation here checks for two arrays whether the first one is a relaxed prefix of the latter. The result is encoded in an integer value with 3 possible outcomes: If -1 is returned, it is not a relaxed prefix. If a value k in [0,pat.length) is returned, then k is the index to be deleted to obtain a prefix. If pat.length is returned, then there is a proper prefix. The example proves in KeY without further user assistance.
