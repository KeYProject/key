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
	private LinkedList<ProcessLauncherListener> listener = new LinkedList<ProcessLauncherListener>();
	private List<ProcessLaunch> running = Collections.synchronizedList(new LinkedList<ProcessLaunch>());

	
	private List<ProcessLaunch> getRunning(){
	    return running;
	}
	
	
	
	private long maxTime = 10000;
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
	    	for(ProcessLaunch launch : running){
	    	    launch.stop();
	    	}
	    	running.clear();
		cancel = true;
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
		listener.add(l);
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
			    launch.start();
			}
	
	
		
	}
	
	protected void checkTime(){
	    	synchronized(getRunning()){
		Iterator<ProcessLaunch> it = getRunning().iterator();
		while(it.hasNext()){
			ProcessLaunch launch = it.next();
			long currentTime = System.currentTimeMillis();
			if(!launch.checkTime(currentTime, maxTime)|| !launch.running()){
			    	boolean time = launch.running();
				launch.stop();
				if(time){
				    publish(new Event(this,launch,Event.Type.INTERRUP_PROCESS));	    
				}
				
				try{
					it.remove();		
				}catch( ConcurrentModificationException e){
				    eventException(launch.getProcess(), e);
				}
						
			}else{
			     publish(new Event(this,launch,Event.Type.PROCESS_STATUS));		
			}
		}
	    	}

	}
	
	
	
	private void remove(Process process){
		process.stop();
		if(running.isEmpty() && queue.isEmpty()){
			runningIsEmpty();
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
		remove(p);	
		publish(new Event(this,launch,Event.Type.PROCESS_EXCEPTION,e));
		
	}


	public void eventFinished(Process p) {
	    	ProcessLaunch launch = findLaunch(p);
		remove(p);
		publish(new Event(this,launch,Event.Type.PROCESS_FINISHED));

	}


	public void eventInterruption(Process p) {
	    	ProcessLaunch launch = findLaunch(p);
		remove(p);
		publish(new Event(this,launch,Event.Type.PROCESS_INTERRUPTION));

	}


	public void eventStarted(Process p) {
	    	ProcessLaunch launch = findLaunch(p);
		publish(new Event(this,launch,Event.Type.PROCESS_START));
		
	}

	
	

	
	public void run() {
		start();
		while(!getCancel()){
			executeNextProcesses();
			checkTime();
			try {
				Thread.currentThread().sleep(SLEEP);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				eventException(null, e);
				
			}
			if(getRunning().isEmpty()){
				runningIsEmpty();
				
			}
			
			
		}
		publish(new Event(this, null,Event.Type.WORK_DONE));
			

		
		

	}
	
	abstract protected void publish(final Event e);


	
        public void eventCycleFinished(Process p,Object userObject) {
            ProcessLaunch launch = findLaunch(p);
            publish(new Event(this,launch,Event.Type.PROCESS_CYCLE_FINISHED,userObject));
	    
        }
        


        
	



}
