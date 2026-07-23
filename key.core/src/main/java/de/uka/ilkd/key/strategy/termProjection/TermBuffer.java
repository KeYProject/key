/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.strategy.costbased.feature.StableCost;

/**
 * A buffer holds no state of its own -- it is a key into the per-evaluation
 * {@link org.key_project.prover.strategy.costbased.MutableState}, so its value during a cost
 * evaluation is whatever the enclosing {@code let} bound in that same evaluation. The locality
 * annotation is looked up on the concrete class (the annotations are not {@code @Inherited}),
 * so this specialization has to repeat the parent's {@link StableCost}.
 */
@StableCost
public class TermBuffer
        extends org.key_project.prover.strategy.costbased.termProjection.TermBuffer<Goal> {
}
