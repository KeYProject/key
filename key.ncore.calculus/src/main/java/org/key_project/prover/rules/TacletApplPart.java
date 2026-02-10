/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.prover.rules.conditions.NewDependingOn;
import org.key_project.prover.rules.conditions.NewVarcond;
import org.key_project.prover.rules.conditions.NotFreeIn;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/// Container for the application part of a Taclet. It contains an assumes-sequent, taclet
/// application restrictions, a list of new
/// variables and a list of variable pairs indicating the NotFreeIn relation, a list of
/// NewDependingOn relations, and a list of general variable conditions.
public record TacletApplPart(Sequent assumesSequent, @NonNull ApplicationRestriction restriction,
        ImmutableList<? extends NewVarcond> varsNew,
        ImmutableList<? extends NotFreeIn> varsNotFreeIn,
        ImmutableList<? extends NewDependingOn> varsNewDependingOn,
        ImmutableList<? extends VariableCondition> variableConditions) {
}
