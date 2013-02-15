// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/** This class is used to store the instantiation of a schemavarible
 * if it is an operator.
 */
public class OperatorInstantiation extends InstantiationEntry {

    /** the term the schemavariable is instantiated with */
    private final Operator op ;

   
    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param op the Operator the SchemaVariable is instantiated with
     */
    OperatorInstantiation(SchemaVariable sv, Operator op) {
	super(sv);
	this.op = op;
    }

    
    /** returns the Operator the SchemaVariable is instantiated with
     */
    public Operator getOperator() {
	return op;
    }

    
    @Override    
    public Object getInstantiation() {
	return op;
    }

    
    @Override
    public String toString() {
	return "[" + getSchemaVariable() + ", " + getOperator() + "]";
    }
}
