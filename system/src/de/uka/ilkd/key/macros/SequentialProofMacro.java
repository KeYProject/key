// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.macros;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.util.ArrayList;

/**
 * The abstract class SequentialProofMacro can be used to create compound macros
 * which sequentially apply macros one after the other. This works only for macros
 * which use {@link KeYMediator#startAutoMode()}.
 *
 * <p>
 * Since {@link ProofMacro}s run asynchronously, the start of the next macro
 * must be performed in a listener call at the end of a autostart.
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
     * Override this method by returning an array with the macros you want to
     * call in the order of execution.
     *
     * @return a non-null array which should not be altered afterwards.
     */
    protected abstract ProofMacro[] createProofMacroArray();

    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable.
     * If there is no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        List<ProofMacro> macros = getProofMacros();
        if(macros.isEmpty()) {
            return false;
        } else {
            return macros.get(0).canApplyTo(mediator, goals, posInOcc);
        }
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * This launches the first macro and registers a new
     * {@link AutoModeListener} with the {@code mediator}. This listener
     * unregisters itself after the last macro.
     *
     * @throws InterruptedException
     *             if one of the wrapped macros is interrupted.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        final List<Node> initNodes = new ArrayList<Node>(goals.size());
        for (Goal goal : goals) {
            initNodes.add(goal.node());
        }
        final Proof proof = initNodes.isEmpty() ?
                mediator.getSelectedProof() : initNodes.get(0).proof();
        final ImmutableList<Goal> gs = initNodes.isEmpty() ?
                proof.openEnabledGoals() : proof.getSubtreeEnabledGoals(initNodes.get(0));
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, gs, proof);
        for (final ProofMacro macro : getProofMacros()) {
            // reverse to original nodes
            for (Node initNode : initNodes) {
                if (macro.canApplyTo(mediator, initNode, posInOcc)) {
                    final ProverTaskListener pml =
                            new ProofMacroListener(macro, listener);
                    pml.taskStarted(macro.getName(), 0);
                    synchronized(macro) {
                        // wait for macro to terminate
                        info = macro.applyTo(mediator, initNode, posInOcc, pml);
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
        if(proofMacros == null) {
            this.proofMacros = createProofMacroArray();
            assert proofMacros != null;
            assert proofMacros.length > 0;
        }
        return Collections.unmodifiableList(Arrays.asList(proofMacros));
    }
}
