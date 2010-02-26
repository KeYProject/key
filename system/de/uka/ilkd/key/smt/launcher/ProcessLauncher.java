package de.uka.ilkd.key.smt.launcher;

import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;



public  class ProcessLauncher  extends TimerTask implements ProcessListener{
    	private final static int SLEEP = 100;
    
	private LinkedList<Process> queue = new LinkedList<Process>();
	private LinkedList<ProcessLauncherListener> listener = new LinkedList<ProcessLauncherListener>();
	private List<ProcessLaunch> running = Collections.synchronizedList(new LinkedList<ProcessLaunch>());
	
	private synchronized List<ProcessLaunch> getRunning(){
	    return running;
	}
	
	private long maxTime = 10000;
	private int counter =0;
	private boolean cancel = false;
	
	public ProcessLauncher(){
		
	}
	

	private synchronized void start(){
		cancel = false;
	}
	
	private synchronized void cancelMe(){
		cancel = true;
	}
	
	
	private synchronized boolean getCancel(){
		return cancel;
	}
	
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
	 * @param maxTime the maxTime to set
	 */
	public void setMaxTime(long maxTime) {
		this.maxTime = maxTime;
	}

	/*@Override
	public void run() {

		counter++;
		executeNextProcesses();
		
		
		checkTime();
	
	}*/
	
	protected void executeNextProcesses(){
		
		for(Process process : queue){
			ProcessLaunch launch = new ProcessLaunch(process);
			launch.start();
			getRunning().add(launch);
		}
		queue.clear();
		
	}
	
	protected void checkTime(){
		Iterator<ProcessLaunch> it = getRunning().iterator();
		while(it.hasNext()){
			ProcessLaunch launch = it.next();
			long currentTime = System.currentTimeMillis();
			if(!launch.checkTime(currentTime, maxTime)|| !launch.running()){
		
				launch.stop();
				try{
					it.remove();		
				}catch( ConcurrentModificationException e){
					
				}
						
			}else{
			
				publish(new Event(this,launch.getProcess(),Event.PROCESS_STATUS));		
			}
		}
		

	}
	
	
	
	private void remove(Process process){
		process.stop();
		//System.out.println(getRunning().size());
		//getRunning().remove(process);
		//System.out.println(getRunning().size());
		if(running.isEmpty()){
			runningIsEmpty();
		}
	}
	
	private void runningIsEmpty(){
		cancelMe();
		publish(new Event(this,null,Event.PROCESS_FINISHED));
	
		
		
	}


	public void eventException(Process p, Exception e) {
		remove(p);	
		publish(new Event(this,p,Event.PROCESS_EXCEPTION));
		System.out.println("exception "+e);
		e.printStackTrace(System.out);
		
	}


	public void eventFinished(Process p) {
		remove(p);
		publish(new Event(this,p,Event.PROCESS_FINISHED));

	}


	public void eventInterruption(Process p) {
		remove(p);
		publish(new Event(this,p,Event.PROCESS_INTERRUPTION));

	}


	public void eventStarted(Process p) {
		publish(new Event(this,p,Event.PROCESS_START));
		
	}
	
	

	
	public void run() {
		System.out.println(queue);
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
			

		
		

	}
	
	private void publish(final Event e){
		
		for(ProcessLauncherListener l : listener){
			l.eventOccured(e);
		}
		/*SwingUtilities.invokeLater(new Runnable() {  
			public void run() {
			
			}
		});*/
	}


	/* (non-Javadoc)
         * @see de.uka.ilkd.key.smt.launcher.ProcessListener#eventCycleFinished(de.uka.ilkd.key.smt.launcher.Process)
         */
        public void eventCycleFinished(Process process) {
            publish(new Event(this,process,Event.PROCESS_CYCLE_FINISHED));
	    
        }
	



}
