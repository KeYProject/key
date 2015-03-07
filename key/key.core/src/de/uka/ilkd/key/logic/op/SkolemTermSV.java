// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;

/**
 * Schema variable that is instantiated with fresh Skolem constants. At the
 * moment, such schema variables have to be accompanied by a "NewDependingOn"
 * varcond, although with the removal of the meta variable mechanism, this
 * would no longer really be necessary.
 */
public final class SkolemTermSV extends AbstractSV {

    /** 
     * Creates a new schema variable that is used as placeholder for
     * skolem terms.
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type     
     * allowed to match a list of program constructs
     */    
    SkolemTermSV(Name name, Sort sort) {
	super(name, sort, true, false);	
	assert sort != Sort.UPDATE;
    }
	
    
    @Override
    public MatchConditions match(SVSubstitute subst, 
	    			 MatchConditions mc,
	    			 Services services) {
	if(subst.equals(mc.getInstantiations().getInstantiation(this))) {
	    return mc;
	} else {
	    return null;
	}
    }
    
    
    @Override
    public String toString() {
	return toString(sort().toString() + " skolem term");
    }
    
    
    @Override
    public String proofToString() {
	return "\\schemaVar " 
	        + (sort() == Sort.FORMULA 
	           ? "\\skolemFormula" 
	           : "\\skolemTerm " + sort().name()) 
	        + " " 
	        + name() 
	        + ";\n";
    }
}