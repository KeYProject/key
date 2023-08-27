/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;

import org.key_project.util.collection.ImmutableList;

/**
 * This macro does nothing and is not applicable. It can be used to create compound macros, e.g. as
 * an alternative macro for {@link DoWhileFinallyMacro}.
 *
 * @author christoph
 */
public class SkipMacro extends AbstractProofMacro {

    @Override
    public String getName() {
        return "SkipMacro";
    }

    @Override
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Does nothing";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        return false;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws InterruptedException {
        // do nothing
        return new ProofMacroFinishedInfo(this, goals);
    }
}
