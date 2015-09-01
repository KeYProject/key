package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;

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
    private int numOfInvokedMacros;
    private ProverTaskListener superordinateListener;
    private String macroName;

    public ProofMacroListener(String macroName, ProverTaskListener listener) {
        this.macroName = macroName;
        this.numOfInvokedMacros = 0;
        this.superordinateListener = listener;
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        numOfInvokedMacros++;
        if (superordinateListener != null) {
            superordinateListener.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro,
                                            macroName
                                            + (macroName.length() == 0
                                                ? "" : " -- ")
                                            + info.getMessage(), info.getSize()));
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

    public int getLevel() {
        return this.numOfInvokedMacros;
    }
}