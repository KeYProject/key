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

import java.util.Iterator;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;

public abstract class ExhaustiveProofMacro implements ProofMacro {

    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        while (posInOcc != null && !posInOcc.isTopLevel()) {
            posInOcc = posInOcc.up();
        }
        PosInTerm posInTerm = PosInTerm.TOP_LEVEL;
        Sequent seq = mediator.getSelectedNode().sequent();
        Iterator<SequentFormula> seqIt = seq.iterator();
        Term term = null;
        SequentFormula seqForm = null;
        PosInOccurrence.findInSequent(seq, 0, posInTerm);
        while (seqIt.hasNext()) {
            seqForm = seqIt.next();
            term = seqForm.formula();
        }
        if (posInOcc != null && posInOcc.posInTerm() != null) {
            PIOPathIterator it = posInOcc.iterator();
            PosInOccurrence subPos = null;
            while (it.next() != -1) {
                subPos = it.getPosInOccurrence();
                if (getProofMacro().canApplyTo(mediator, subPos)) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        assert posInOcc != null;
        while (!posInOcc.isTopLevel()) {
            posInOcc = posInOcc.up();
        }
        if (posInOcc.posInTerm() != null) {
            PIOPathIterator it = posInOcc.iterator();
            PosInOccurrence subPos = null;
            while (it.next() != -1) {
                subPos = it.getPosInOccurrence();
                if (getProofMacro().canApplyTo(mediator, subPos)) {
                    getProofMacro().applyTo(mediator, subPos, listener);
                    return;
                }
            }
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