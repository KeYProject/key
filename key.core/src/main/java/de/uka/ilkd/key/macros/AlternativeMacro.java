/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.List;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

import org.key_project.util.collection.ImmutableList;

/**
 * The abstract class AlternativeMacro can be used to create compound macros which apply the first
 * applicable macro (similar to a shortcut disjunction) and then it returns.
 *
 * @author Michael Kirsten
 */
public abstract class AlternativeMacro extends AbstractProofMacro {

    /**
     * The proof macro alternatives in their order according to their priority.
     *
     * This array is created on demand using {@link #createProofMacroArray()}.
     */
    private ProofMacro[] proofMacros = null;

    /**
     * Creates the proof macro array.
     *
     * Override this method by returning an array with the macro alternatives of which you want to
     * call the first applicable one in the order of their priority.
     *
     * @return a non-null array which should not be altered afterwards.
     */
    protected abstract ProofMacro[] createProofMacroArray();

    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if any one of the macros is applicable. If
     * there is no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        final List<ProofMacro> macros = getProofMacros();
        for (ProofMacro macro : macros) {
            if (macro.canApplyTo(proof, goals, posInOcc)) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * This launches the first applicable macro of {@link #getProofMacros()}.
     *
     * @throws InterruptedException if the macro is interrupted.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws Exception {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        for (final ProofMacro macro : getProofMacros()) {
            if (macro.canApplyTo(proof, goals, posInOcc)) {
                final ProverTaskListener pml = new ProofMacroListener(macro.getName(), listener);
                pml.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
                synchronized (macro) {
                    // wait for macro to terminate
                    info = macro.applyTo(uic, proof, goals, posInOcc, pml);
                }
                pml.taskFinished(info);
                // change source to this macro ... [TODO]
                info = new ProofMacroFinishedInfo(this, info);
                return info;
            }
        }
        return info;
    }

    /**
     * Gets the proof macros.
     *
     * @return the proofMacros as an unmodifiable list.
     */
    public List<ProofMacro> getProofMacros() {
        if (proofMacros == null) {
            this.proofMacros = createProofMacroArray();
            assert proofMacros != null;
            assert proofMacros.length > 0;
        }
        return List.of(proofMacros);
    }
}
