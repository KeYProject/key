package de.uka.ilkd.key.smt.launcher;

import java.io.IOException;
import java.util.TimerTask;

public interface Process extends Runnable {
	void setProcessListener(ProcessListener listener);
	void stop();
	String getTitle();
	boolean running();

	
}
