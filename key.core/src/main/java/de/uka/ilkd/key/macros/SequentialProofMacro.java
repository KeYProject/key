/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

import org.key_project.util.collection.ImmutableList;

/**
 * The abstract class SequentialProofMacro can be used to create compound macros which sequentially
 * apply macros one after the other. This works only for macros which use
 * {@link KeYMediator#startAutoMode()}.
 *
 * <p>
 * Since {@link ProofMacro}s run asynchronously, the start of the next macro must be performed in a
 * listener call at the end of a autostart.
 *
 * @author mattias ulbrich
 */
public abstract class SequentialProofMacro extends AbstractProofMacro {

    /**
     * The proof macros to be applied in their order.
     *
     * This array is created on demand using {@link #createProofMacroArray()}.
     */
    private ProofMacro[] proofMacros = null;

    /**
     * Creates the proof macro array.
     *
     * Override this method by returning an array with the macros you want to call in the order of
     * execution.
     *
     * @return a non-null array which should not be altered afterwards.
     */
    protected abstract ProofMacro[] createProofMacroArray();

    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable. If there is
     * no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        List<ProofMacro> macros = getProofMacros();
        if (macros.isEmpty()) {
            return false;
        } else {
            return macros.get(0).canApplyTo(proof, goals, posInOcc);
        }
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * This launches the first macro and registers a new {@link AutoModeListener} with the
     * {@code mediator}. This listener unregisters itself after the last macro.
     *
     * @throws InterruptedException if one of the wrapped macros is interrupted.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws Exception {
        final List<Node> initNodes = new ArrayList<>(goals.size());
        for (Goal goal : goals) {
            initNodes.add(goal.node());
        }
        final ImmutableList<Goal> gs = initNodes.isEmpty() ? proof.openEnabledGoals()
                : proof.getSubtreeEnabledGoals(initNodes.get(0));
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, gs, proof, false);
        for (final ProofMacro macro : getProofMacros()) {
            // reverse to original nodes
            for (Node initNode : initNodes) {
                if (macro.canApplyTo(initNode, posInOcc)) {
                    final ProverTaskListener pml =
                        new ProofMacroListener(macro.getName(), listener);
                    pml.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
                    synchronized (macro) {
                        // wait for macro to terminate
                        info = macro.applyTo(uic, initNode, posInOcc, pml);
                    }
                    pml.taskFinished(info);
                    info = new ProofMacroFinishedInfo(this, info);
                }
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
