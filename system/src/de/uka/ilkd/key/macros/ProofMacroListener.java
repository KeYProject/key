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
        assert message != null;
        numOfInvokedMacros++;
        superordinateListener.taskStarted(getMacro().getName() + " -- " + message, size);
    }

    @Override
    public void taskProgress(int position) {
        superordinateListener.taskProgress(position);
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        numOfInvokedMacros--;
        superordinateListener.taskFinished(info);
    }

    public ProofMacro getMacro() {
        return this.macro;
    }

    public int getLevel() {
        return this.numOfInvokedMacros;
    }
}