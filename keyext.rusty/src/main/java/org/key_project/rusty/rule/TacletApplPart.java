/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.logic.Sequent;
import org.key_project.util.collection.ImmutableList;

public record TacletApplPart(Sequent assumesSequent, ImmutableList<NewVarcond> varsNew,
                             ImmutableList<NotFreeIn> varsNotFreeIn,
                             ImmutableList<NewDependingOn> varsNewDependingOn,
                             ImmutableList<VariableCondition> variableConditions) {
}
