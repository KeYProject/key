This example has been an assignment during a tutorial for Verifast.

For the sake of comparison, you can find annotated C source code for the Verifast tool in the src-directory.

Most proof obligations are verifiable without user interaction. Only the JML depends clause (id: 7 - <inv> for Transaction) needs few interactions 
(Translating the limited version self.next.<inv>$lmt to the unlimited one).

We model bank accounts using two classes. Accounts do not store there balance explicitly but rather as a linked list of their transactions. We need to specify and verify that transactions of different accounts do not interfere.

Benchmark by Bart Jacobs
KeY version by Mattias Ulbrich <ulbrich@kit.edu>
