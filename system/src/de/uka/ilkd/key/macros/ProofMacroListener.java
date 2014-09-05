package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;

/**
 * Listener for the application of proof macros (which may be run in
 * a separate worker thread). They work in a mutual way by also storing
 * a reference to the superordinate listener on the level above.
 * Additionally, an integer for remembering how many proof macros have
 * been invoked by the according macro is stored. This integer is especially
 * important in console mode in order to know when to finish batch mode.
 * In GUI mode, the proof macro names are being displayed in the status bar.
 *
 * @author Michael Kirsten
 */
public class ProofMacroListener implements ProverTaskListener {
    private ProofMacro macro;
    private int numOfInvokedMacros;
    private ProverTaskListener superordinateListener;

    public ProofMacroListener(ProofMacro macro, ProverTaskListener listener) {
        this.macro = macro;
        this.numOfInvokedMacros = 0;
        this.superordinateListener = listener;
    }

    @Override
    public void taskStarted(String message, int size) {
        numOfInvokedMacros++;
        final String macroName = getMacro().getName();
        if (superordinateListener != null) {
            superordinateListener.taskStarted(macroName
                                            + (macroName.length() == 0
                                                ? "" : " -- ")
                                            + message, size);
        }
    }

    @Override
    public void taskProgress(int position) {
        if (superordinateListener != null) {
            superordinateListener.taskProgress(position);
        }
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        numOfInvokedMacros--;
        if (superordinateListener != null) {
            superordinateListener.taskFinished(info);
        }
    }

    public ProofMacro getMacro() {
        return this.macro;
    }

    public int getLevel() {
        return this.numOfInvokedMacros;
    }
}