package de.uka.ilkd.key.smt.launcher;

import java.io.IOException;
import java.io.InputStream;


abstract public class AbstractProcess implements  Process
{
	private static ProcessBuilder builder = new ProcessBuilder();


	private java.lang.Process   process;
	private ProcessListener listener;
	private long runningTime = 0;
	boolean running = true;
	public synchronized boolean running(){
	   return running; 
	}
	
	
	void setRunningTime(long time){
		runningTime = time;
	}

	
	public AbstractProcess() {
		super();
			
	}
	
	public void setProcessListener(ProcessListener l){
		listener = l;
	}




	public String getTitle() {		
		return "";
	}


	public void stop() {
	    	running = false;
		if(process != null){
			process.destroy();
		}
	}
	
	public String toString(){
		return getTitle();
	}


	public void run() {
		int exitCode =0;
		boolean end = false;
		try {
	            do{
	            try {
	            	String [] command = atStart();
	            	
	            	builder.command(command);
	            	
	            	process = builder.start();
	            	listener.eventStarted(this);
	            	
	            	exitCode = process.waitFor();
	            
	            } catch (InterruptedException e) {
	            	listener.eventInterruption(this);
	            	return;
	            }catch (Exception e) {
	            	listener.eventException(this, e);
	            	return;
	            } 
	            
	            	end = atEnd(process.getInputStream(),process.getErrorStream(),exitCode);
	            	listener.eventCycleFinished(this);
	            }while(!end);
                } catch (Exception e) {
                    listener.eventException(this, e);
                }
		listener.eventFinished(this);				
	}
	
	public long getRunningTime(){
		return runningTime;
		
	}
	
	public abstract String [] atStart() throws Exception;
	
	public abstract boolean atEnd(InputStream result, InputStream error, int exitStatus) throws Exception;
	
}

