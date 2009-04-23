// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.termgenerator;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;


/**
 * Interface for objects that generate lists/sequences of terms or formulas.
 * This interface is used in the feature <code>ForEachCP</code> in order to
 * instantiate schema variables with different terms/formulas.
 */
public interface TermGenerator {
    IteratorOfTerm generate(RuleApp app, PosInOccurrence pos, Goal goal);
}
