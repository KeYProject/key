package de.uka.ilkd.key.smt.launcher;

public interface ProcessListener {
	void eventException(Process p , Exception e);
	void eventInterruption(Process p);
	void eventFinished(Process p);
	void eventStarted(Process p);
	/**
         * @param abstractProcess
         */
        void eventCycleFinished(Process process, Object userObject);
	
}
