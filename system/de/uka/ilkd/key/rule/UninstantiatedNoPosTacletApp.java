// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;


/**
 * A subclass of <code>NoPosTacletApp</code> for the special case of a
 * taclet app without any instantiations. The method
 * <code>setupMatchConditions</code> is overwritten to avoid object
 * creations.
 */
class UninstantiatedNoPosTacletApp extends NoPosTacletApp {

    /**
     * @param taclet
     */
    UninstantiatedNoPosTacletApp (Taclet taclet) {
        super ( taclet );
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.NoPosTacletApp#setupMatchConditions(de.uka.ilkd.key.logic.PosInOccurrence, de.uka.ilkd.key.java.Services, de.uka.ilkd.key.logic.Constraint)
     */
    protected MatchConditions setupMatchConditions (PosInOccurrence pos,
                                                    Services services,
                                                    Constraint userConstraint) {
        if ( taclet() instanceof RewriteTaclet )
            return ((RewriteTaclet)taclet ()).checkUpdatePrefix
            ( pos, MatchConditions.EMPTY_MATCHCONDITIONS, services, userConstraint );

        return MatchConditions.EMPTY_MATCHCONDITIONS;
    }
}
