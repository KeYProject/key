package de.uka.ilkd.key.smt.launcher;

public class Event {
        public enum Type  {
	PROCESS_START,PROCESS_INTERRUPTION,
	PROCESS_FINISHED,PROCESS_EXCEPTION,
	WORK_DONE,PROCESS_STATUS,PROCESS_CYCLE_FINISHED,
	INTERRUP_PROCESS};
	private ProcessLauncher launcher;
	private ProcessLaunch   launch;
	private Type		 type;
	private Object          userObject;
	public Event(ProcessLauncher l, ProcessLaunch launch, Type type){
		launcher = l;
		this.launch = launch;
		this.type = type;
	}
	
	public  Event(ProcessLauncher l, ProcessLaunch launch, Type type, Object object){
	    this(l, launch, type);
	    userObject = object;
	    
	}

	public ProcessLauncher getLauncher() {
		return launcher;
	}


	public ProcessLaunch getLaunch() {
		return launch;
	}


	public Type getType() {
		return type;
	}
	
	public Object getUserObject(){
	    return userObject; 
	}

	
}
