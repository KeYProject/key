package de.uka.ilkd.key.smt.launcher;

public class Event {
	public final static int PROCESS_START = 0;
	public final static int PROCESS_INTERRUPTION = 1;
	public final static int PROCESS_FINISHED = 2;
	public final static int PROCESS_EXCEPTION = 3;
	public final static int WORK_DONE = 4;
	public final static int PROCESS_STATUS = 5;
	public final static int PROCESS_CYCLE_FINISHED = 6;
	private ProcessLauncher launcher;
	private Process 		process;
	private int				type;
	public Event(ProcessLauncher l, Process p, int type){
		launcher = l;
		process = p;
		this.type = type;
	}

	public ProcessLauncher getLauncher() {
		return launcher;
	}


	public Process getProcess() {
		return process;
	}


	public int getType() {
		return type;
	}

	
}
