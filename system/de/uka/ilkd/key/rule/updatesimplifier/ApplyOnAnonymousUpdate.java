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
 * Created on 09.12.2004
 */
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.Debug;

/**
 * Applies an update U on an anonymous update A. Only the latter one survives.  
 * @author bubel
 */
public class ApplyOnAnonymousUpdate extends AbstractUpdateRule {

    /**
     * create an instance of this rule
     * @param updateSimplifier
     */
    public ApplyOnAnonymousUpdate(UpdateSimplifier updateSimplifier) {
        super(updateSimplifier);        
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.UpdateRule#isApplicable(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public boolean isApplicable(Update update, Term target) {        
        return target.op() instanceof AnonymousUpdate;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.UpdateRule#apply(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public Term apply(Update update, Term target, Services services) {        
        logEnter(update, target);
        Term result = updateSimplifier().simplify(target, services);
        logExit(result);
        return result;
    }

    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        // an anonymous update is not a location
        Debug.fail ( "matchingCondition(...) must not be called for target "
                     + target );
        return null; // unreachable
    }
}
