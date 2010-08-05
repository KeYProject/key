package de.uka.ilkd.key.smt.launcher;
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

/**
 * This class describes the current execution of a process.
 *  
 *  */
public class ProcessLaunch{
	private Process process;
	private Thread  thread;
	private long    startTime = 0;
	private long usedTime  =0;
	

	
	/**
	 * @return {@link Process}
	 */
	boolean running(){
	    return process.running();
	}
	

	ProcessLaunch(Process process){
		this.process = process;
	}
	
	/**
	 * Starts the process belonging to this launch:
	 * A new daemon thread will be started.
	 */
	void start(){
	        process.init();
		thread = new Thread(process,process.getTitle());
		thread.setDaemon(true);
		thread.start();
		
		startTime = System.currentTimeMillis();
	}
	
	/**
	 * Stops the process by interrupting it.
	 */
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
	
	/**
	 * @param currentTime current time in ms. 
	 * @return the running time of the process in ms.
	 */
	public long runningTime(long currentTime){
		if(!process.running()){
		    return 0;
		}
		usedTime = currentTime - startTime; 
		return usedTime;
	}
	
	public long usedTime(){
	    return usedTime;
	}
	
	/**
	 * 
	 * @return returns the process belonging to this launch.
	 */
	public Process getProcess(){
		return process;
	}
	
	public boolean getInterrupted(){
	    return ((AbstractProcess)process).getInterrupted();
	}
	
	public boolean equals(Object o){
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