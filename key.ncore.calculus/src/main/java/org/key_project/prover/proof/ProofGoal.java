/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

public interface ProofGoal<G extends ProofGoal<G>> {
    ProofObject<G> proof();

    Sequent<? extends SequentFormula> sequent();
}
