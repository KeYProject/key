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

package de.uka.ilkd.key.gui.macros;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;

public abstract class AlternativeProofMacro implements ProofMacro {

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
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        List<ProofMacro> macros = getProofMacros();
        for (int i = 0; i < macros.size(); i++) {
            if (macros.get(i).canApplyTo(mediator, posInOcc)) {
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
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        for (ProofMacro macro : getProofMacros()) {
            if(macro.canApplyTo(mediator, posInOcc)) {
                macro.applyTo(mediator, posInOcc, listener);
                return;
            }
        }
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

    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}