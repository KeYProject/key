package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;

public class ProofMacroListener implements ProverTaskListener {
    private ProofMacro macro;
    private int numOfInvokedMacros;

    public ProofMacroListener(ProofMacro macro) {
        this.macro = macro;
        this.numOfInvokedMacros = 0;
    }

    @Override
    public void taskStarted(String message, int size) {
        assert message != null;
        numOfInvokedMacros++;
    }

    @Override
    public void taskProgress(int position) {
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        macro.innerMacroFinished(info);
        numOfInvokedMacros--;
    }

    public ProofMacro getMacro() {
        return this.macro;
    }
}