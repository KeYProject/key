// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** 
 * returns a reference to <traInitialized>
 */
public class MetaTraInitialized extends MetaField {

    public MetaTraInitialized() {
	super("#traInitialized");
    }

    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, 
			  Services services) {	
        return termFactory.createAttributeTerm
	    (services.getJavaInfo().getAttribute
	     (ImplicitFieldAdder.IMPLICT_ARRAY_TRA_INITIALIZED, 
	      services.getJavaInfo().getKeYJavaType(term.sub(0).sort())),
	     term.sub(0));
    }

}
