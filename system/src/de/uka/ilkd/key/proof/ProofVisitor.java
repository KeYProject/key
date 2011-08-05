package de.uka.ilkd.key.proof;

public interface ProofVisitor {
        public void visit(Proof proof, Node visitedNode);
}
