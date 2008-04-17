// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

class VariableSV extends SortedSchemaVariable {

    /** creates a new SchemaVariable. That is used as placeholder for
     * bound(quantified) variables.
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type     
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of quantified variables
     */
    VariableSV(Name name, Sort sort, boolean listSV) {
	super(name, QuantifiableVariable.class, sort, listSV); 	
    }
    
    /** returns true iff this SchemaVariable is used to match
     * bound (quantifiable) variables 
     * @return true iff this SchemaVariable is used to match
     * bound (quantifiable) variables 
     */
    public boolean isVariableSV() {
	return true;
    }
    
    public boolean isRigid () {
	return true;
    }
    
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#match(de.uka.ilkd.key.logic.op.SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions 
    	match(SVSubstitute substitute, MatchConditions mc, Services services) {                
        final Term subst;
        if (substitute instanceof LogicVariable) {
            subst = TermFactory.DEFAULT.createVariableTerm((LogicVariable)substitute);
        } else if (substitute instanceof Term && 
                ((Term)substitute).op() instanceof QuantifiableVariable) {
            subst = (Term) substitute;
        } else {
            Debug.out("Strange Exit of match in VariableSV. Check for bug");
            return null;
        }
        final Term foundMapping = (Term)mc.getInstantiations ().
        	getInstantiation(this);
        if (foundMapping == null) {            		
            return addInstantiation(subst, mc, services);
        } else if (((QuantifiableVariable)foundMapping.op()) != subst.op()) {
            return null; //FAILED;			    
        } 
        return mc;
    } 
    
    
    /** toString */
    public String toString() {
	return toString("variable");
    }

}
