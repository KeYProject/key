/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termgenerator;

import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.NonNull;


/// Interface for objects that generate lists/sequences of terms or formulas. This interface is used
/// in the feature <code>ForEachCP</code> in order to instantiate schema variables with different
/// terms/formulas.
public interface TermGenerator<@NonNull Goal extends ProofGoal<@NonNull Goal>> {
    Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState);
}
