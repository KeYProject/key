example.path = Information Flow
example.name = Simple E-Voting
example.additionalFile.1 = src/simple_evoting/Setup.java
example.additionalFile.2 = src/simple_evoting/Server.java
example.additionalFile.3 = src/simple_evoting/Voter.java
example.additionalFile.4 = src/simple_evoting/Message.java
example.additionalFile.5 = src/simple_evoting/SMT.java
example.additionalFile.6 = src/simple_evoting/NetworkClient.java
example.additionalFile.7 = src/simple_evoting/SMTEnv.java
example.additionalFile.8 = src/simple_evoting/Environment.java

Information flow example.

The example is a simplified version of an evoting case-study that we are investigating in cooperation with the group of Ralf Küsters at the University of Trier. This version has already been verified with KeY, the information flow part as well as the functional part.

Voters send their secrete votes (encrypted, but this not modeled throughout in this version) over a channel (for instance the internet) to a server. The server counts the votes for the different parties. After all voters voted, the result of the election is published. The order in which voters vote (and whether a voter votes at all) is decided by an adversary which is able to control the channel. The result of the election is declassified.

The difficult part in this case-study is to show that indeed only the correct result of the election is declassified.


