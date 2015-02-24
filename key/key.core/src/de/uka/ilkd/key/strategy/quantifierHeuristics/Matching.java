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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;

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
    public static ImmutableSet<Substitution> basicMatching(Trigger trigger,
                                                  Term targetTerm) {
        return BasicMatching.getSubstitutions ( trigger.getTriggerTerm (),
                                                targetTerm );
    }

    public static ImmutableSet<Substitution> twoSidedMatching(UniTrigger trigger,
                                                     Term targetTerm, 
                                                     TermServices services) {
        TwoSidedMatching tsm = new TwoSidedMatching ( trigger, targetTerm, services );
        return tsm.getSubstitutions (services);
    }      
    
}