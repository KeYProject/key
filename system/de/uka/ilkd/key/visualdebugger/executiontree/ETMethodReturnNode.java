// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;

/**
 * This execution tree node is used to represent a node referring to a return
 * step of a method. FIXME: the copy method creates insane trees (I do currently
 * no understand what ITNodes are, but most probably the copy method brings
 * ETNodes and ITNodes out of sync), up to now I am not sure which behaviour of
 * copy has been wanted. This bug applies to all subclasses as well.
 */
public class ETMethodReturnNode extends ETNode {

    /**
     * represents the symbolic return value of the method
     */
    private final Term result;

    /**
     * creates an instance of the ETNode
     * 
     * @param bc
     * @param itNodes
     * @param result
     * @param parent
     */
    public ETMethodReturnNode(ImmutableList<Term> bc, LinkedList itNodes, Term result,
            ETNode parent) {
        super(bc, itNodes, parent);
        this.result = result;

    }

    public ETMethodReturnNode(ImmutableList<Term> bc, Term result, ETNode parent) {
        super(bc, parent);
        this.result = result;

    }

    /**
     * creates a shallow copy of this node and attaches it to node <tt>p</tt>
     * FIXME: FIX this method as it creates not well linked trees Problems: 1)
     * the children of this node are not linked to their new parent -->
     * malformed tree 2) the children are not copied themselves and linking
     * would destroy the old tree
     * 
     */
    public ETNode copy(ETNode p) {
        ETNode copy = new ETMethodReturnNode(getBC(), (LinkedList) getITNodes()
                .clone(), result, p);
        copy.setChildren((LinkedList) getChildrenList().clone());
        return copy;
    }

    /**
     * the symbolic value of the method result
     * 
     * @return the symbolic value of the method result
     */
    public Term getResult() {
        return result;
    }

}
