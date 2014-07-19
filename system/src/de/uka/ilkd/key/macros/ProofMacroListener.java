package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;

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