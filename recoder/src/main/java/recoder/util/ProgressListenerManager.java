/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

import java.util.concurrent.CopyOnWriteArrayList;

/**
 * Helper class that handles progress listener registration and broadcasts. Caches and reuses the
 * event object, so listeners should not store the event object.
 *
 * @author AL
 * @since 0.72
 */
public final class ProgressListenerManager {
    private final ReuseableProgressEvent progressEvent;
    private final Object source;

    /**
     * list of progress listeners; the list is a copy-on-write list and thread-safe, but
     * expensive when adding/removing listeners. It is justified as easiest working solution as
     * the addition and removal of listeners is performed far less than iterating over the list and
     * the number of listeners is usually small
     */
    private final CopyOnWriteArrayList<ProgressListener> progressListeners =
        new CopyOnWriteArrayList<>();

    /**
     * creates the manager for progress listeners
     *
     * @param source the Object where the progress hopefull occurs
     */
    public ProgressListenerManager(Object source) {
        this.source = source;
        progressEvent = new ReuseableProgressEvent(source, 0, 0, null);
    }

    public ProgressEvent getLastProgressEvent() {
        return progressEvent;
    }

    public void fireProgressEvent(int workCount) {
        if (!progressListeners.isEmpty()) {
            progressEvent.setWorkDoneCount(workCount);
            for (var pl : progressListeners) {
                pl.workProgressed(progressEvent);
            }
        }
    }

    public void fireProgressEvent(int workCount, Object state) {
        if (!progressListeners.isEmpty()) {
            progressEvent.setWorkDoneCount(workCount);
            progressEvent.setState(state);
            for (var pl : progressListeners) {
                pl.workProgressed(progressEvent);
            }
        }
    }

    public void fireProgressEvent(int workCount, int newMaximum) {
        if (!progressListeners.isEmpty()) {
            progressEvent.setWorkDoneCount(workCount);
            progressEvent.setWorkToDoCount(newMaximum);
            for (var pl : progressListeners) {
                pl.workProgressed(progressEvent);
            }
        }
    }

    public void fireProgressEvent(int workCount, int newMaximum, Object state) {
        if (!progressListeners.isEmpty()) {
            progressEvent.setWork(workCount, newMaximum, state);
            for (var pl : progressListeners) {
                pl.workProgressed(progressEvent);
            }
        }
    }

    public void addProgressListener(ProgressListener l) {
        progressListeners.addIfAbsent(l);
    }

    public void removeProgressListener(ProgressListener chl) {
        progressListeners.remove(chl);
    }

    private static class ReuseableProgressEvent extends ProgressEvent {

        /**
         * serialization id
         */
        private static final long serialVersionUID = -8120253607435943831L;

        public ReuseableProgressEvent(Object source, int workDone, int workToDo, Object state) {
            super(source, workDone, workToDo, state);
        }
    }
}
