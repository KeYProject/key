package de.uka.ilkd.key.smt;

import java.util.TimerTask;

public final class ExecutionWatchDog extends TimerTask {

    private int timeout;

    private Process proc;

    private long starttime = -1;
    
    private boolean wasInterrupted = false;

    /**
     * Construct a new Watch dog.
     * @param timeout after this amount of seconds, p is cancelled.
     * @param p The Process that should be watched.
     */
    public ExecutionWatchDog(int timeout, Process p) {
	super();
	this.timeout = timeout;
	this.proc = p;
	this.wasInterrupted = false;
    }

    @Override
    public void run() {
	if (starttime < 0) {
	    this.starttime = System.currentTimeMillis();
	}

	if (System.currentTimeMillis() - this.starttime > timeout * 1000) {
	    this.wasInterrupted = true;
	    proc.destroy();
	}

    }
    
    public boolean wasInterrupted() {
	return this.wasInterrupted;
    }

}
