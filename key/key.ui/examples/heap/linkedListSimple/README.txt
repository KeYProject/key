Simple specification of a linked list to illustrate non-functional represents clauses. The verification goal is to show that there are no cycles of length 1.
Author: Daniel Bruns <bruns@kit.edu>
Steps to prove: The precondition of foo() is "index == index". This is to ensure that index syntactically occurs in the sequent in order to trigger the represents clause taclet. Perform that rule. Then the proof can be completed automatically.
