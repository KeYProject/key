/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.control;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskFinishedInfo;
import org.key_project.prover.engine.TaskStartedInfo;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A composite structure for prover task listeners. For the moment, this is only used for the
 * application of proof macros at the outermost level.
 *
 * @author Michael Kirsten
 */
@NullMarked
public class CompositePTListener implements ProverTaskListener {
    private final @Nullable ProverTaskListener[] listeners;

    /**
     * Creates a composite listener over the given listeners. Null elements are tolerated and
     * skipped by the dispatch methods.
     *
     * @param l the listeners to combine, possibly containing null entries
     */
    public CompositePTListener(@Nullable ProverTaskListener[] l) {
        this.listeners = l;
    }

    public CompositePTListener(@Nullable ProverTaskListener ptl1,
            @Nullable ProverTaskListener ptl2) {
        this(new ProverTaskListener[] { ptl1, ptl2 });
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        for (ProverTaskListener l : listeners) {
            if (l != null) {
                l.taskStarted(info);
            }
        }
    }

    @Override
    public void taskProgress(int position) {
        for (ProverTaskListener l : listeners) {
            if (l != null) {
                l.taskProgress(position);
            }
        }
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        for (int i = listeners.length - 1; 0 <= i; i--) {
            ProverTaskListener l = listeners[i];
            if (l != null) {
                l.taskFinished(info);
            }
        }
    }
}
