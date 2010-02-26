package de.uka.ilkd.key.smt.launcher;

class ProcessLaunch{
	private Process process;
	private Thread  thread;
	private long    startTime = 0;

	
	
	boolean running(){
	    return process.running();
	}
	

	ProcessLaunch(Process process){
		this.process = process;
	}
	
	void start(){
		thread = new Thread(process,process.getTitle());
		
		thread.start();
		startTime = System.currentTimeMillis();
	}
	
	synchronized void stop(){
	    	process.stop();
		if(thread!=null){
			thread.interrupt();
			thread = null;
			
		}
	}
	
	boolean checkTime(long currentTime, long maxTime){
		
		return runningTime(currentTime) < maxTime;

	}
	
	long runningTime(long currentTime){
		
		return currentTime - startTime;
	}
	
	Process getProcess(){
		return process;
	}
	
	public boolean equals(Object o){
	    	System.out.println("equals: " + o);
		if(o instanceof ProcessLaunch){
			return o == this;
		}
		if(o instanceof Process){
			return o == this.process;
		}
		if(o instanceof Thread){
			return o == this.thread;
		}
		return false;
	}
	
	public String toString(){
	    return process.toString();
	}
	
	
	
	
}