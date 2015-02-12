example.name = List with Sequences
example.path = Dynamic Frames
example.additionalFile.1 = src/List.java
example.additionalFile.2 = src/ArrayList.java
example.additionalFile.3 = src/LinkedList.java
example.additionalFile.4 = src/Node.java
example.additionalFile.5 = src/TestList.java
example.additionalFile.6 = src/SimplifiedLL.java


A list interface with addition and removal operation, an array list
and a linked list implementation, and a test class that uses the list
in a non-trivial way.

Unlike the examples in directory "list", this approach uses the
abstract datatype "sequence" (\seq in JML) to abstract from the actual
implementation structure. In particular, for the linked list, the
chain of nodes is abstracted by a sequence of nodes such that no
recursive definitions are needed.

The proofs for ArrayList require straight forward interaction or run
automatically.

The proofs for LinkedList require more interaction but can all be 
proved.

The class SimplifiedLL.java contains specification and code for a
specification/verification comparison with examples in directory
../list_recursiveSpec.

Apr 2012, M.U.
