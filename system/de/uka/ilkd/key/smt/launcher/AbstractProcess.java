package de.uka.ilkd.key.smt.launcher;

import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.smt.MakesProgress;
import de.uka.ilkd.key.smt.SMTProgressMonitor;


abstract public class AbstractProcess implements  Process, MakesProgress
{
	private static ProcessBuilder builder = new ProcessBuilder();
	protected Collection<SMTProgressMonitor> monitors = new LinkedList<SMTProgressMonitor>();

	private java.lang.Process   process;
	protected ProcessListener listener;
	private long runningTime = 0;
	boolean running = false;
	private int currentCycle = 0;
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






	public void init(){
	    running = true;
	    currentCycle = 0;
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
	            	
	          	end = atEnd(process.getInputStream(),process.getErrorStream(),exitCode);
	          	
	            
	         
	            	currentCycle++;
	            	
	            
	            } catch (InterruptedException e) {
	            	listener.eventInterruption(this);
	            	return;
	            }catch (Exception e) {
	            	listener.eventException(this, e);
	            	return;
	            } 
	            
	          
	            }while(!end);
                } catch (Exception e) {
                    listener.eventException(this, e);
                    return;
                }
		listener.eventFinished(this);				
	}
	
	public long getRunningTime(){
		return runningTime;
		
	}
	
	public abstract String [] atStart() throws Exception;
	
	public abstract boolean atEnd(InputStream result, InputStream error, int exitStatus) throws Exception;
	
        public void addProgressMonitor(SMTProgressMonitor p) {
		monitors.add(p);    	
        }


   
        public void interrupt() {
            stop();
            listener.eventInterruption(this);
        }


 
        public void removeAllProgressMonitors() {
            monitors.clear();
	
        }

        public boolean removeProgressMonitor(SMTProgressMonitor p) {
            return monitors.remove(p);
        }
        
        public Collection<SMTProgressMonitor> getMonitors(){
            return monitors;
        }
        
        public int getCurrentCycle(){
            return currentCycle;
        }
        
        

	
}

