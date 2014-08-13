package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;

/**
 * A composite structure for prover task listeners.
 * For the moment, this is only used for the application
 * of proof macros at the outermost level.
 *
 * @author Michael Kirsten
 */
public class CompositePTListener implements ProverTaskListener {
    private ProverTaskListener[] listeners;

    public CompositePTListener(ProverTaskListener[] l) {
        this.listeners = l;
    }

    public CompositePTListener(ProverTaskListener ptl1,
                               ProverTaskListener ptl2) {
        this(new ProverTaskListener[]{ptl1, ptl2});
    }

    @Override
    public void taskStarted(String message, int size) {
        for (ProverTaskListener l: listeners) {
            if (l != null) {
                l.taskStarted(message, size);
            }
        }
    }

    @Override
    public void taskProgress(int position) {
        for (ProverTaskListener l: listeners) {
            if (l != null) {
                l.taskProgress(position);
            }
        }
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        for (int i = listeners.length -1; 0 <= i; i--) {
            ProverTaskListener l = listeners[i];
            if (l != null) {
                l.taskFinished(info);
            }
        }
    }
}
