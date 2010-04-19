package de.uka.ilkd.key.smt.launcher;

import java.util.Collection;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;

import de.uka.ilkd.key.smt.MakesProgress;
import de.uka.ilkd.key.smt.SMTProgressMonitor;
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

/** This class is used to start several processes in the same time. 
 *  
 */
public abstract  class ProcessLauncher  implements ProcessListener, Runnable{
    	private final static int SLEEP = 10;
    
	private List<Process> queue = Collections.synchronizedList(new LinkedList<Process>()); 
	protected LinkedList<ProcessLauncherListener> listener = new LinkedList<ProcessLauncherListener>();
	private List<ProcessLaunch> running = Collections.synchronizedList(new LinkedList<ProcessLaunch>());
	private boolean firstClosePolicy = true;
	private int runningCounter =0;
	

	
	public boolean isFirstClosePolicy() {
            return firstClosePolicy;
        }

	public void setFirstClosePolicy(boolean firstClosePolicy) {
            this.firstClosePolicy = firstClosePolicy;
        }

	private List<ProcessLaunch> getRunning(){
	    return running;
	}
	
	
	
	private long maxTime = 5000;
	private int counter =0;
	private boolean cancel = false;
	
	
	public void init(){
	    queue.clear();
	    running.clear();
	}
	
	public ProcessLauncher(){
		
	}
	
	
	private synchronized void start(){
		cancel = false;
	}
	
	protected synchronized void cancelMe(){
	        cancel = true;
	    	for(ProcessLaunch launch : running){
	    	    launch.stop();
	    	}
	    	running.clear();
		
	}
	
	
	private synchronized boolean getCancel(){
		return cancel;
	}
	
	/**
	 * adds a process to the list of processes 
	 * that will be started by the <code>ProcessLauncher</code>
	 * @param process 
	 */
	public void addProcess(Process process){
	    	
		process.setProcessListener(this);
		queue.add(process);
	}
	
	public void addListener(ProcessLauncherListener l){
	        if(!listener.contains(l)){
	    		listener.add(l);
	        }
	
	}
	
	public void removeListener(ProcessLauncherListener l){
		listener.remove(l);
	}
	
	/**
	 * @return the maxTime
	 */
	public long getMaxTime() {
		return maxTime;
	}

	/**
	 * @param maxTime the maxTime to be set
	 */
	public void setMaxTime(long maxTime) {
		this.maxTime = maxTime;
	}


	
	protected void executeNextProcesses(){
		if(queue.isEmpty() || !running.isEmpty()){
		    return;
		}
		for(Process process : queue){
			ProcessLaunch launch = new ProcessLaunch(process);
			getRunning().add(launch);
                        
		
		}

		queue.clear();
	
			for(ProcessLaunch launch : running){
			    runningCounter++;
			    launch.start();
			    
			}
	
	
	
		
	}
	
	protected void checkProcesses(){
	     try{
	      synchronized(getRunning()){
		Iterator<ProcessLaunch> it = getRunning().iterator();
		
		while(it.hasNext()){
			ProcessLaunch launch = it.next();
			long currentTime = System.currentTimeMillis();
		
			if(!launch.checkTime(currentTime, maxTime)|| !launch.running()){
			    	boolean time = launch.running();
				launch.stop();
				if(time || launch.getInterrupted()){
				    publish(new Event(this,launch,Event.Type.INTERRUP_PROCESS));	    
				} else {
				    processFinished(launch);
				    publish(new Event(this,launch,Event.Type.PROCESS_FINISHED));
				}
				it.remove();		
				
						
			}else{
			     publish(new Event(this,launch,Event.Type.PROCESS_STATUS));		
			}
		}
	    	}
	     }catch( ConcurrentModificationException e){
		    eventException(null, e);
	      }
	     

	}
	
	private void processFinished(ProcessLaunch launch){
	    if(launch.getProcess().wasSuccessful() && firstClosePolicy){
		cancel = true;
	    }
	}
	
	
	
	
	private void runningIsEmpty(){
		cancelMe();
		
	}
	
	private ProcessLaunch findLaunch(Process p){
	    synchronized(running){
	    for(ProcessLaunch launch : running){
		if(launch.getProcess() == p){
		    return launch;
		}
	    }
	    }
	   return null;
	}


	
	public void eventException(Process p, Exception e) {
	    	ProcessLaunch launch = findLaunch(p);
			
		publish(new Event(this,launch,Event.Type.PROCESS_EXCEPTION,e));
	
		
		
	}


	public void eventFinished(Process p) {
	}


	public void eventInterruption(Process p) {
	}


	public void eventStarted(Process p) {
	}

	

	
	public void run() {
		start();
		while(!getCancel()){
			executeNextProcesses();
			checkProcesses();
			try {
				Thread.currentThread().sleep(SLEEP);
			} catch (InterruptedException e) {
			    eventException(null, e);
				
			}
			if(getRunning().isEmpty()||runningCounter==0){
				runningIsEmpty();
				
			}
			
			
		}
		cancelMe();
		publish(new Event(this, null,Event.Type.WORK_DONE));
		

		
		

	}
	
	abstract protected void publish(final Event e);
	

	
        public void eventCycleFinished(Process p,Object userObject) {
            ProcessLaunch launch = findLaunch(p);
            publish(new Event(this,launch,Event.Type.PROCESS_CYCLE_FINISHED,userObject));
	    
        }
        


        
	



}
