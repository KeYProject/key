/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.strategy.costbased.feature.StableCost;

/**
 * Stable like its base class (locality annotations are not inherited, so the subclass must repeat
 * the marker): the buffer only reads back the per-evaluation value written by the enclosing
 * {@code let} within the same cost evaluation; the stability of that value is the business of the
 * projection that fills the buffer, which is classified separately.
 */
@StableCost
public class TermBuffer
        extends org.key_project.prover.strategy.costbased.termProjection.TermBuffer<Goal> {
}
