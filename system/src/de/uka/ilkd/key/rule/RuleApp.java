// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


/**
 * rule application with specific information how and where the rule
 * has to be applied
 */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

public interface RuleApp {

    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and
     * a position in the corresponding formula) of this rule application
     */
    PosInOccurrence posInOccurrence();

    /** applies the specified rule at the specified position
     * if all schema variables have been instantiated
     * @param goal the Goal where to apply the rule
     * @param services the Services encapsulating all java information
     * @return list of new created goals
     */
    ImmutableList<Goal> execute(Goal goal, Services services);

    /** returns true if all variables are instantiated
     * @return true if all variables are instantiated
     */
    boolean complete();

}
