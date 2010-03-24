// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/*
 * Created on 22.12.2004
 */
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigid;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.Debug;

/**
 * @author bubel
 * This rule is fall back rule for "unknown" terms with non rigid
 * top level symbol and just prepends the Update.
 */
public class ApplyOnNonRigidTerm extends AbstractUpdateRule {

    /**
     * @param updateSimplifier the UpdateSimplifier to which this 
     * rule is attached
     */
    public ApplyOnNonRigidTerm(UpdateSimplifier updateSimplifier) {
        super(updateSimplifier);        
    }

    /**
     * this rule is applicable if the top level operator is a non rigid 
     * symbol
     */
    public boolean isApplicable(Update update, Term target) {       
        return target.op() instanceof NonRigid;
    }

    /** 
     * implementation of the fall back rule for terms with an "unknown"
     * non rigid top level symbol
     */
    public Term apply(Update update, Term target, Services services) {       
	
        return UpdateSimplifierTermFactory.DEFAULT.
            createUpdateTerm(update.getAllAssignmentPairs(), 
                    updateSimplifier().simplify(target, services));
    }

    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        // we don't really know what to do here ;-)
        Debug.fail ( "no default implementation of "
                     + "matchingCondition(...) available" );
        return null; // unreachable
    }
}
