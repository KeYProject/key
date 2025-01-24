/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;


/**
 * Interface for objects that generate lists/sequences of terms or formulas. This interface is used
 * in the feature <code>ForEachCP</code> in order to instantiate schema variables with different
 * terms/formulas.
 */
public interface TermGenerator {
    Iterator<org.key_project.logic.Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState);
}
