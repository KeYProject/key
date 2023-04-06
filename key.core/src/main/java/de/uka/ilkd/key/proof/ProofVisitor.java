package de.uka.ilkd.key.proof;

public interface ProofVisitor {
    void visit(Proof proof, Node visitedNode);
}
