package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;

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
        for (ProverTaskListener l: listeners) {
            if (l != null) {
                l.taskFinished(info);
            }
        }
    }
}
