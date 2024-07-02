example.name = 1 - Sparse Arrays
example.path = Benchmarks/VACID-0
example.additionalFile.1 = src/Harness.java
example.additionalFile.2 = src/SparseArray.java
example.additionalFile.3 = src/MemoryAllocator.java


The first challenge from the paper "VACID-0: Verification of Ample Correctness of Invariants of Data-structures, Edition 0" by Rustan Leino and Michal Moskal:

An array where all three basic operations (create, get, and set) take constant time.

So far only a partial solution (assume instead of assert at the critical point).

Interactive proofs:
-SparseArray::set (uncomment additional requires clause; switch off quantifier instantiation; use Simplify)
