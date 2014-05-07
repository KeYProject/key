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

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;

public abstract class ExhaustiveProofMacro implements ProofMacro {

    private static boolean isApplicableRecursive(KeYMediator mediator,
                                                 PosInOccurrence posInOcc,
                                                 ProofMacro macro) {
        if (macro.canApplyTo(mediator, posInOcc)) {
            return true;
        } else if (posInOcc == null || posInOcc.posInTerm() == null) {
            return false;
        }
        for (int i = 0; i < posInOcc.constrainedFormula().formula().subs().size(); i++) {
            if (posInOcc.subTerm().depth() > 0
                    && isApplicableRecursive(mediator, posInOcc.down(i), macro)) {
                return true;
            }
        }
        return false;
    }

    private static void applyRecursive(KeYMediator mediator,
                                       PosInOccurrence posInOcc,
                                       ProofMacro macro,
                                       ProverTaskListener listener) throws InterruptedException {
        if (macro.canApplyTo(mediator, posInOcc)) {
            macro.applyTo(mediator, posInOcc, listener);
        } else if (posInOcc == null || posInOcc.posInTerm() == null) {
            return;
        }
        for (int i = 0; i < posInOcc.constrainedFormula().formula().subs().size(); i++) {
            if (posInOcc.subTerm().depth() > 0
                    && isApplicableRecursive(mediator, posInOcc.down(i), macro)) {
                applyRecursive(mediator, posInOcc.down(i), macro, listener);
                return;
            }
        }
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        final ProofMacro macro = getProofMacro();
        assert macro != null;
        assert mediator != null;
        assert mediator.getSelectionModel() != null;
        if (mediator.getSelectedNode() == null) {
            return macro.canApplyTo(mediator, posInOcc);
        }
        final Sequent seq = mediator.getSelectedNode().sequent();
        for (int i = 1; i <= seq.size(); i++) {
            if (isApplicableRecursive(mediator,
                                      PosInOccurrence.findInSequent(seq, i, PosInTerm.TOP_LEVEL),
                                      macro)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        final Sequent seq = mediator.getSelectedNode().sequent();
        final ProofMacro macro = getProofMacro();
        for (int i = 1; i <= seq.size(); i++) {
            applyRecursive(mediator, PosInOccurrence.findInSequent(seq, i, PosInTerm.TOP_LEVEL),
                           macro, listener);
        }
    }

    /**
     * Gets the proof macros.
     *
     * @return the proofMacro.
     */
    abstract ProofMacro getProofMacro();

    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}