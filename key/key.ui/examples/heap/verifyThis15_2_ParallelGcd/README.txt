example.name = Parallel Gcd
example.path = Benchmarks/VerifyThis2015
example.additionalFile.1 = src/ParallelGcd.java
example.proofFile = parallelGcd.proof

This is the second challenge from the VerifyThis competition @ ETAPS 2015 organized by M. Huisman, R. Klebanov, and R. Monahan.

The implementation computes the greatest common divisor (gcd) of two positive integers a and b in a pseudo parallel manner as following:

WHILE a != b DO
    CHOOSE(
         IF a > b THEN a := a - b ELSE SKIP FI,
         IF b > a THEN b := b - a ELSE SKIP FI
    )
OD;
OUTPUT a

The specification makes use of a model method, which determines the gcd of a and b, including some invariants about the gcd.