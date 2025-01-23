/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofObject;

/**
 * An information object with additional information about the finished task.
 */
public interface TaskFinishedInfo {

    Object getSource();

    Object getResult();

    long getTime();

    int getAppliedRules();

    int getClosedGoals();

    ProofObject<?> getProof();

}
