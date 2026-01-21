package de.uka.ilkd.key.logic;

/**
 * This abstract Vistor class declares the interface for a common term visitor.
 */
public abstract class DefaultVisitor implements Visitor {
    @Override
    public boolean visitSubtree(Term visited) {
        return true;
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {
    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {
    }
}
