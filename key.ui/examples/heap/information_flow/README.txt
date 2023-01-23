A collection of examples for modelling dependencies / secure information flow using ghost state.

* ArrayList: A variation of the ArrayList class from the "list" example, where the proof obligations for the dependency contracts have been encoded into ghost state and method contracts. These method contract proof obligations should be verifiable without direct user interaction. The regular dependency proof obligations are meaningless here.

* UpdateAbstraction: Examples from the paper "Abstract Interpretation of Symbolic Execution with Explicit State Updates" by Richard Bubel, Reiner Haehnle and Benjamin Weiss.
  - ex7_1_insecure: Insecure, and thus not verifiable.
  - ex7_2_insecure: Insecure, and thus not verifiable.
  - ex7_3_secure: Verifiable.
  - ex7_4_secure: Verifiable.
  - ex7_5_secure: Verifiable.
  - ex7_6_secure: Verifiable.
  - ex7_7_secure: Not verifiable, because of loss of precision in encoding.
  - ex7_8_secure: Not verifiable, because of loss of precision in encoding.
  - ex9_secure: Verifiable.
  