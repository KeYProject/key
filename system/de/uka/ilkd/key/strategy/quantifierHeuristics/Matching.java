// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * Two kind of matching algorithm are coded in two nested classes BaseMatching
 * TwosideMatching 
 */
class Matching {

    private Matching(){}
    
    /**
     * matching <code>trigger</code> to <code>targetTerm</code> recursively
     * @param trigger       a uni-trigger
     * @param targetTerm    a gound term
     * @return all substitution found from this matching
     */
    public static SetOfSubstitution basicMatching(Trigger trigger,
                                                  Term targetTerm) {
        return BasicMatching.getSubstitutions ( trigger.getTriggerTerm (),
                                                targetTerm );
    }

    public static SetOfSubstitution twoSidedMatching(UniTrigger trigger,
                                                     Term targetTerm, 
                                                     Services services) {
        TwoSidedMatching tsm = new TwoSidedMatching ( trigger, targetTerm );
        return tsm.getSubstitutions (services);
    }      
    
}
