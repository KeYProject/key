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

import de.uka.ilkd.key.logic.op.AnonymousUpdate;

/**
 * This is currently only used for anonymous updates, 
 * for general (quantified) updates that is an own class 
 * <code>QuanUpdateTerm</code>
 */
public class UpdateTerm extends OpTerm.UnaryOpTerm {

    /** 
     * creates a UpdateTerm
     * @param op the UpdateOperator
     * @param subs an array of Term
     */
    UpdateTerm(AnonymousUpdate op, Term[] subs) {	
	super(op, subs);
    }
 
    public JavaBlock executableJavaBlock() {
	return sub(arity()-1).javaBlock();
    }

    /** toString */
    public String toString() {
	StringBuffer sb = new StringBuffer ( "{" );
        sb.append ( op ().name () );
        sb.append ( "}" );
        sb.append ( sub ( arity () - 1 ) );
        return sb.toString ();
    }

}
