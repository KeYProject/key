package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.LinkedList;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;


public class AutomaticProver {

       private ReentrantLock lock = new ReentrantLock();
       private Condition   sleepCondition = lock.newCondition();
       private ReentrantLock awaitShutdown = new ReentrantLock();
       
       
       public void start(Proof proof, int maxNumberOfRules, long timeout) throws InterruptedException{
	   Worker worker = new Worker(proof, maxNumberOfRules);
	   try{
	       lock.lock();
	 
	       Thread thread = new Thread(worker);
	       thread.start();
	       if(timeout < 0){
		sleepCondition.await();
	       }else {
		sleepCondition.await(timeout, TimeUnit.MILLISECONDS);
		thread.interrupt();
	       }       
	   }catch (InterruptedException e) {
	       // Interruption is okay
           }
	   finally{
	     lock.unlock();   
	     awaitShutdown.lock();
	     if(worker.getException()!= null ){
		 if(worker.getException() instanceof InterruptedException){
		     throw (InterruptedException) worker.getException();
		 }
		 throw new RuntimeException(worker.getException());
	     }
	   }   
       }
       
       private class Worker implements Runnable{
        private Proof proof;
        private int   maxNumberOfRules;
        private Throwable exception;
	   
	   
        
	public Worker(Proof proof, int maxNumberOfRules) {
	    super();
	    this.proof = proof;
	    this.maxNumberOfRules = maxNumberOfRules;
        }

	private LinkedList<Goal> copyGoals(ImmutableList<Goal> goals){
	    LinkedList<Goal> result = new LinkedList<Goal>();
	    for(Goal goal : goals){
		result.add(goal);
	    }
	    return result;
	}
	
	public Throwable getException() {
	    return exception;
        }
	
	public void run(){
	   try{
	   awaitShutdown.lock();    
	   LinkedList<Goal> openGoals = copyGoals(proof.openGoals()); 
	   int ruleCounter =0;
	   while (!openGoals.isEmpty() && ruleCounter < maxNumberOfRules) { 
	     Goal goal = openGoals.getFirst();
	     RuleApp app = getNextApp(goal);
	     if (app == null) {
        	 openGoals.removeFirst();
             }else{
        	 ImmutableList<Goal> goals = goal.apply(app);
        	 for(Goal res : goals){
        	     if(!res.equals(goal)){
        		 openGoals.add(res);
        	     }
        	 }
        	 ruleCounter++;
        	 if(goal.node().isClosed()){
        	     openGoals.removeFirst();
        	 }
             }	     
	   }
	   }catch(Throwable e){
	     exception = e;
	   }finally{
	      lock.lock();
	    sleepCondition.signalAll();
	    lock.unlock();	
	    awaitShutdown.unlock();
	   }
	 }
	
	private RuleApp getNextApp(Goal goal) {
	     RuleApp app = goal.getRuleAppManager().next();
	     if(app == null) {
	      	goal.ruleAppIndex().scanBuiltInRules(goal);
	       	app = goal.getRuleAppManager().next();
	     }
	     return app;
	}
    
      }
    
}
