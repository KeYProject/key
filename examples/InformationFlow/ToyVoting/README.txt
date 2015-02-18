example.path = Information Flow
example.name = Toy Voting
example.additionalFile.1 = src/Voter.java

Information flow example.

The example is a toy implementation of a voting process. The vote of every voter is read and send over a not further modelled network. If the read vote is not valid, then 0 is send instead to indicate abstention. The votes itself and whether a vote is valid is secrete. At the end the participation is output.

Without the optimisations described in the FM-Paper the verification of the method secure_voting() with the help of self-composition is very expensive or even infeasible.

