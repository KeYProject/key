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


package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;

/**
 * Buit-in rule interface.
 * As applications of this rule kind may
 * not be successful in each case one has to ensure that the goal split is
 * done only iff the application was successful.
 */
public interface BuiltInRule extends Rule {

    /**
     * returns true iff a rule is applicable at the given
     * position. This does not necessarily mean that a rule application
     * will change the goal (this decision is made due to performance
     * reasons)
     */
    boolean isApplicable(Goal goal, PosInOccurrence pio);

    IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services);
}