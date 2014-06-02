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
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.util.Debug;
import javax.swing.SwingWorker;

/**
 * The Class ProofMacroWorker is a swing worker for the application of proof
 * macros.
 *
 * It decouples proof macros from the GUI event thread. It registers with the
 * mediator to receive Stop-Button events
 */
public class ProofMacroWorker extends SwingWorker<Void, Void> implements InterruptListener {

    /**
     * The macro which is to be executed
     */
    private final ProofMacro macro;

    /**
     * The mediator of the environment
     */
    private final KeYMediator mediator;

    /**
     * This position may be null if no subterm selected
     */
    private final PosInOccurrence posInOcc;

    /**
     * Instantiates a new proof macro worker.
     *
     * @param macro the macro, not null
     * @param mediator the mediator, not null
     * @param posInOcc the position, possibly null
     */
    public ProofMacroWorker(ProofMacro macro, KeYMediator mediator, PosInOccurrence posInOcc) {
        assert macro != null;
        assert mediator != null;
        this.macro = macro;
        this.mediator = mediator;
        this.posInOcc = posInOcc;
    }

    @Override
    protected Void doInBackground() throws Exception {
        try {
            macro.applyTo(mediator, posInOcc, mediator.getUI());
        } catch (final InterruptedException exception) {
            Debug.out("Proof macro has been interrupted:");
            Debug.out(exception);
        } catch (final Exception exception) {
            // This should actually never happen.
            ExceptionDialog.showDialog(MainWindow.getInstance(), exception);
        }
        return null;
    }

    @Override
    public void interruptionPerformed() {
        cancel(true);
    }

    @Override
    protected void done() {
        mediator.setInteractive(true);
        mediator.startInterface(true);
        mediator.removeInterruptedListener(this);
    }
}
