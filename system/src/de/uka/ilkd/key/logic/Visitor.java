package de.uka.ilkd.key.logic;

public interface Visitor {
    /**
     * the entry method for the visitor pattern
     * @param visited the Term to be visited
     */
    public abstract void visit(Term visited);

    /**
     * this method is called in execPreOrder and execPostOrder in class Term
     * when entering the subtree rooted in the term subtreeRoot.
     * Default implementation is to do nothing. Subclasses can
     * override this method 
     * when the visitor behaviour depends on informations bound to subtrees.
     * @param subtreeRoot root of the subtree which the visitor enters.
     */

    public void subtreeEntered(Term subtreeRoot);

    /**
     * this method is called in execPreOrder and execPostOrder in class Term
     * when leaving the subtree rooted in the term subtreeRoot.
     * Default implementation is to do nothing. Subclasses can
     * override this method 
     * when the visitor behaviour depends on informations bound to subtrees.
     * @param subtreeRoot root of the subtree which the visitor leaves.
     */

    public void subtreeLeft(Term subtreeRoot);
}
