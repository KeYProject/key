package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.TimerTask;

public final class ExecutionWatchDog extends TimerTask {

    private int timeout;

    private ArrayList<Process> procList = new ArrayList<Process>();

    private long starttime = -1;
    
    private boolean wasInterrupted = false;

    /**
     * Construct a new Watch dog.
     * @param timeout after this amount of seconds, p is canceled.
     * @param p The Process that should be watched.
     */
    public ExecutionWatchDog(int timeout, Process p) {
	super();
	this.timeout = timeout;
	this.procList.add(p);
	this.wasInterrupted = false;
    }
    
    /**
     * Construct a new Watch dog.
     * @param timeout after this amount of seconds, the processes are canceled.
     * @param pl the list of processes that should be watched.
     */
    public ExecutionWatchDog(int timeout, ArrayList<Process> pl)
    {
	super();
	this.timeout = timeout;
	this.procList.addAll(pl);
	this.wasInterrupted = false;
    }

    @Override
    public void run() {
	
	if (starttime < 0) {
	    this.toBeInterrupted = false;
	    this.starttime = System.currentTimeMillis();
	}

	if (this.toBeInterrupted) {
	    for(Process proc: procList)
	    proc.destroy();
	}
	
	if (System.currentTimeMillis() - this.starttime > timeout) {
	    this.wasInterrupted = true;
	    for(Process proc: procList)
	    proc.destroy();
	}

    }
    
    public boolean wasInterruptedByTimeout() {
	return this.wasInterrupted;
    }
    
    public boolean wasInterruptedByUser() {
	return this.toBeInterrupted;
    }
    
    private boolean toBeInterrupted = false;
    
    public void interrupt() {
	this.toBeInterrupted = true;
    }
    
    /**
     * 
     * @return the progress made since start. Value between 0 and 99.
     */
    public int getProgress() {
	if (this.starttime < 0) {
	    return 0;
	} else {
	    int toReturn = (((int)(System.currentTimeMillis() - starttime)*100) / timeout);
	    if (toReturn < 0) {
		return 0;
	    } else if (toReturn > 99) {
		return 99;
	    } else {
		return toReturn;
	    }
	}
    }

}
