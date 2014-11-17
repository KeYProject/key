// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
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
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

/**
 * The abstract class AlternativeMacro can be used to create compound macros
 * which apply the first applicable macro (similar to a shortcut disjunction)
 * and then it returns.
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
     * Override this method by returning an array with the macro alternatives of
     * which you want to call the first applicable one in the order of their priority.
     *
     * @return a non-null array which should not be altered afterwards.
     */
    protected abstract ProofMacro[] createProofMacroArray();

    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if any one of the macros is applicable.
     * If there is no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        final List<ProofMacro> macros = getProofMacros();
        for (int i = 0; i < macros.size(); i++) {
            if (macros.get(i).canApplyTo(mediator, goals, posInOcc)) {
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
     * @throws InterruptedException
     *             if the macro is interrupted.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                    ImmutableList<Goal> goals,
                                    PosInOccurrence posInOcc,
                                    ProverTaskListener listener) throws InterruptedException {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        for (final ProofMacro macro : getProofMacros()) {
            if(macro.canApplyTo(mediator, goals, posInOcc)) {
                final ProverTaskListener pml =
                        new ProofMacroListener(macro, listener);
                pml.taskStarted(macro.getName(), 0);
                synchronized(macro) {
                    // wait for macro to terminate
                    info = macro.applyTo(mediator, goals, posInOcc, pml);
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
        if(proofMacros == null) {
            this.proofMacros = createProofMacroArray();
            assert proofMacros != null;
            assert proofMacros.length > 0;
        }
        return Collections.unmodifiableList(Arrays.asList(proofMacros));
    }
}