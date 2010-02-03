// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigidHeapDependentFunction;
import de.uka.ilkd.key.rule.UpdateSimplifier;

/**
 * This rule deals with locations that are only heap dependent, i.e. they do not  
 * depend on local program variables.
 */
public class ApplyOnHeapDependentLocation extends ApplyOnModality {
    public ApplyOnHeapDependentLocation(UpdateSimplifier updateSimplifier, 
            boolean deletionEnabled) {
        super(updateSimplifier, deletionEnabled);        
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.IUpdateRule#isApplicable(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public boolean isApplicable(Update update, Term target) {                
        return target.op() instanceof NonRigidHeapDependentFunction;         
    }
}
