package de.uka.ilkd.key.smt.launcher;

import java.io.IOException;
import java.util.Collection;
import java.util.TimerTask;

import de.uka.ilkd.key.smt.MakesProgress;
import de.uka.ilkd.key.smt.SMTProgressMonitor;

public interface Process extends Runnable,MakesProgress {
	void setProcessListener(ProcessListener listener);
	void stop();
	String getTitle();
	boolean running();
	Collection<SMTProgressMonitor> getMonitors();
	long getRunningTime();
	void init();
	int getCurrentCycle();
	int getMaxCycle();

	
}
