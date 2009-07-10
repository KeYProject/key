// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import java.util.HashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

public class ModalOperatorSV extends OperatorSV  {
    
    /** creates a new SchemaVariable. That is used as placeholder for
     * modal operators.
     * @param name the Name of the SchemaVariable
     * @param arity the arity of the modal operators matched by this SV
     * @param modalities modal operators matched by this SV
     */    
    ModalOperatorSV(Name name, int arity, HashSet modalities) {
        super(name, Modality.class, Sort.FORMULA, arity, modalities);	
    }
    

    @Override
    public boolean additionalValidTopLevel(Term term){
	boolean result = true;
	for(int i=0;i<term.arity(); i++)
	    result = result && term.sub(i).sort().equals(Sort.FORMULA);
	return result;
    }

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be
     * changed by modalities
     */
    public boolean isRigid (Term term) {
	return (term.javaBlock ().isEmpty());
    }    
    
    /**
     * (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#match(SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {        
        if (!(subst instanceof Modality)) {
            Debug.out("FAILED. ModalitySV matches only modalities (template, orig)",
                    this, subst);
            return null;
        }  
        return super.match(subst, mc, services);
    }
     

    public String toString() {
	return toString(" (modal operator)");
    }

}
