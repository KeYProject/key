/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.prover.rules.conditions.NewDependingOn;
import org.key_project.prover.rules.conditions.NewVarcond;
import org.key_project.prover.rules.conditions.NotFreeIn;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;

public record TacletApplPart(Sequent assumesSequent,ImmutableList<?extends NewVarcond>varsNew,ImmutableList<?extends NotFreeIn>varsNotFreeIn,ImmutableList<?extends NewDependingOn>varsNewDependingOn,ImmutableList<?extends VariableCondition>variableConditions){}
