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


package de.uka.ilkd.key.rule;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/** This class is used to collect all appearing SchemaVariables that are bound in a
 * Taclet. Duplicates are not removed becaues the use of persistent
 * datastructure and up to now we just have a SetAsList-implementaion
 * causing to have O(sqr(n)) if it would used. 
 * The class is used by RuleApps to compute all non-instantiated variables.
*/
public class TacletVariableSVCollector extends TacletSchemaVariableCollector {

    /**
     * visits term t in post order 
     * ({@link Term#execPostOrder(de.uka.ilkd.key.logic.Visitor)})
     * and collects all bound schema variables 
     * @param t the Term to be visited (<code>t</code> must not be <code>null</code>  
     */  
    public void visit(Term t) {
	for (int j=0; j<t.arity(); j++) {
	    for (int i=0;i<t.varsBoundHere(j).size();i++) {
		QuantifiableVariable boundVar = t.varsBoundHere(j).
		    get(i);
		if (boundVar instanceof SchemaVariable) {
		    varList = varList.prepend((SchemaVariable)boundVar);
		}
	    }	    
	}
    }
    
}
