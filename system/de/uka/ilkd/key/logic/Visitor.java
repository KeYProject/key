// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

/**
 * This abstract Vistor class declares the interface for a common term visitor.
 */
public abstract class Visitor {	

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

    public void subtreeEntered(Term subtreeRoot){
    }

    /**
     * this method is called in execPreOrder and execPostOrder in class Term
     * when leaving the subtree rooted in the term subtreeRoot.
     * Default implementation is to do nothing. Subclasses can
     * override this method 
     * when the visitor behaviour depends on informations bound to subtrees.
     * @param subtreeRoot root of the subtree which the visitor leaves.
     */

    public void subtreeLeft(Term subtreeRoot){
    }
    
}
