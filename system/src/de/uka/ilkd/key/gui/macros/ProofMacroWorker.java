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

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.InterruptListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SwingWorker3;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.util.Debug;

/**
 * The Class ProofMacroWorker is a swing worker for the application of proof macros.
 * 
 * It decouples proof macros from the GUI event thread.
 * It registers with the mediator to receive Stop-Button events
 */
public class ProofMacroWorker extends SwingWorker3 implements InterruptListener {

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
     * @param macro
     *            the macro, not null
     * @param mediator
     *            the mediator, not null
     * @param posInOcc
     *            the position, possibly null
     */
    public ProofMacroWorker(ProofMacro macro, KeYMediator mediator, PosInOccurrence posInOcc) {
        assert macro != null;
        assert mediator != null;
        this.macro = macro;
        this.mediator = mediator;
        this.posInOcc = posInOcc;
    }

    /* 
     * actually execute the macro. InterruptionException are ignored. All other exceptions
     * are reported in the GUI.
     */
    @Override 
    public Object construct() {
        try {
            macro.applyTo(mediator, posInOcc, mediator.getUI());
        } catch(InterruptedException ex) {
            Debug.out("Proof macro has been interrupted:");
            Debug.out(ex);
        } catch (Exception e) {
            // This should actually never happen.
            ExceptionDialog.showDialog(MainWindow.getInstance(), e);
        }

        // no result is being calculated
        return null;
    }

    /* 
     * initiate the GUI stuff and relay to superclass
     */
    @Override 
    public void start() {
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(this);
        super.start();
    }

    /* 
     * finalise the GUI stuff
     */
    @Override 
    public void finished() {
        mediator.setInteractive(true);
        mediator.startInterface(true);
        mediator.removeInterruptedListener(this);
    }

    /* 
     * If an interruption occured, tell the Swingworker thread
     */
    @Override 
    public void interruptionPerformed() {
        // just notify the thread that the button has been pressed
        interrupt();
    }

}
