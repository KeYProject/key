// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
/** This class is used to store the instantiation of a schemavarible
 * if it is a term.
 */

public class TermInstantiation extends InstantiationEntry {

    /** the term the schemavariable is instantiated with */
    private final Term term ;

    private static final RigidnessException RIGIDNESS_EXCEPTION = new RigidnessException
    ( "Tried to instantiate a rigid schema variable" +
      " with a non-rigid term/formula" );

    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param term the Term the SchemaVariable is instantiated with
     */
    TermInstantiation(SchemaVariable sv, Term term) {
	super(sv);
	this.term = term;
	if ( !term.isRigid () && sv.isRigid () ) {
	    throw RIGIDNESS_EXCEPTION;
	}
    }
    
    /** returns the Term the SchemaVariable is instantiated with
     * @return  the Term the SchemaVariable is instantiated with
     */
    public Term getTerm() {
	return term;
    }

    /** returns the instantiation of the SchemaVariable 
     * @return  the instantiation of the SchemaVariable 
    */
    public Object getInstantiation() {
	return term;
    }

    /** toString */
    public String toString() {
	return "["+getSchemaVariable()+", "+getTerm()+"]";
    }

}
