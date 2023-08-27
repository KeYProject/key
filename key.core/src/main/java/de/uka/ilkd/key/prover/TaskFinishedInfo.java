/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover;

import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;

/**
 * An information object with additional information about the finished task.
 */
public interface TaskFinishedInfo {
    /**
     * The task that has finished. May be one of:
     * <ul>
     * <li>{@link ProofMacro}</li>
     * <li>{@link de.uka.ilkd.key.prover.impl.ApplyStrategy}</li>
     * <li>{@link de.uka.ilkd.key.core.KeYMediator} (when pruning)</li>
     * <li>{@link de.uka.ilkd.key.gui.mergerule.MergeRuleMenuItem}
     * (when applying a merge rule)</li>
     * <li>{@link de.uka.ilkd.key.proof.io.ProblemLoader} (when loading a proof)</li>
     * </ul>
     *
     * @return the source
     */
    Object getSource();

    Object getResult();

    long getTime();

    int getAppliedRules();

    int getClosedGoals();

    Proof getProof();

}
