package recoder.util;

/**
 * Helper class that handles progress listener registration and broadcasts.
 * Caches and reuses the event object, so listeners should not store the event
 * object.
 * 
 * @author AL
 * @since 0.72
 */
public final class ProgressListenerManager {

    private class ReuseableProgressEvent extends ProgressEvent {

        public ReuseableProgressEvent(Object source, int workDone, int workToDo, Object state) {
            super(source, workDone, workToDo, state);
        }
    }

    private final ReuseableProgressEvent progressEvent;

    private final Object source;

    private ProgressListener[] progressListeners = new ProgressListener[0];

    public ProgressListenerManager(Object source) {
        this.source = source;
        progressEvent = new ReuseableProgressEvent(source, 0, 0, null);
    }

    public ProgressEvent getLastProgressEvent() {
        return progressEvent;
    }

    public void fireProgressEvent(int workCount) {
        int length = progressListeners.length;
        if (length > 0) {
            progressEvent.setWorkDoneCount(workCount);
            for (int i = 0; i < length; i++) {
                progressListeners[i].workProgressed(progressEvent);
            }
        }
    }

    public void fireProgressEvent(int workCount, Object state) {
        int length = progressListeners.length;
        if (length > 0) {
            progressEvent.setWorkDoneCount(workCount);
            progressEvent.setState(state);
            for (int i = 0; i < length; i++) {
                progressListeners[i].workProgressed(progressEvent);
            }
        }
    }

    public void fireProgressEvent(int workCount, int newMaximum) {
        int length = progressListeners.length;
        if (length > 0) {
            progressEvent.setWorkDoneCount(workCount);
            progressEvent.setWorkToDoCount(newMaximum);
            for (int i = 0; i < length; i++) {
                progressListeners[i].workProgressed(progressEvent);
            }
        }
    }

    public void fireProgressEvent(int workCount, int newMaximum, Object state) {
        int length = progressListeners.length;
        if (length > 0) {
            progressEvent.setWork(workCount, newMaximum, state);
            for (int i = 0; i < length; i++) {
                progressListeners[i].workProgressed(progressEvent);
            }
        }
    }

    public void addProgressListener(ProgressListener l) {
        synchronized (progressListeners) {
            int length = progressListeners.length;
            ProgressListener[] newListeners = new ProgressListener[length + 1];
            System.arraycopy(progressListeners, 0, newListeners, 0, length);
            newListeners[length] = l;
            progressListeners = newListeners;
        }
    }

    public void removeProgressListener(ProgressListener chl) {
        synchronized (progressListeners) {
            int length = progressListeners.length;
            for (int i = length - 1; i >= 0; i -= 1) {
                if (progressListeners[i] == chl) {
                    ProgressListener[] newListeners = new ProgressListener[length - 1];
                    if (i > 0) {
                        System.arraycopy(progressListeners, 0, newListeners, 0, i);
                    }
                    if (i < length - 1) {
                        System.arraycopy(progressListeners, i + 1, newListeners, i, length - 1 - i);
                    }
                    progressListeners = newListeners;
                    break;
                }
            }
        }
    }
}