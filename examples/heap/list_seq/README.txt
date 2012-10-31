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
