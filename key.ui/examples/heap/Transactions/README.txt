example.name = Transaction
example.path = Dynamic Frames
example.additionalFile.1 = src/Account.java
example.additionalFile.2 = src/Transaction.java
example.additionalFile.3 = verifast-assignment2.c

This example has been an assignment during a tutorial for Verifast.

We model bank accounts using two classes. Accounts do not store there balance explicitly but rather as a linked list of their transactions. We need to specify and verify that transactions of different accounts do not interfere.

For the sake of comparison, you can find annotated C source code for the Verifast tool in the src-directory.

Most proof obligations are verifiable without user interaction. Only the JML accessible clause (id: 7 - <inv> for Transaction) needs few interactions 
(Translating the limited version self.next.<inv>$lmt to the unlimited one).

Due to incompatibilities in the KeY storage mechanism, you are encouraged to switch to revision 87dc0a69f156a44363f4ffda80eda512f68e3bd1 to load the saved proofs.

Benchmark by Bart Jacobs
KeY version by Mattias Ulbrich <ulbrich@kit.edu>
