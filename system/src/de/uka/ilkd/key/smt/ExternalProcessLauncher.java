// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;


import java.io.IOException;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;


/**
 * This class is responsible for starting external processes:
 * 1. It creates the process
 * 2. Creates a pipe, that is used for communication.
 * 3. Starts the process and waits until the pipe has been closed or the process has been stopped.
 * Remark: It blocks the invoking thread.
 * The parameter T of the class can be used to define user-specific parameters.
 */
public class ExternalProcessLauncher<T> {
	private Process process;
	/**lock for the process-object in order to guarantee synchronous access: If you want to access on <code>process</code>
	 * then acquire first the lock!*/        
	private ReentrantLock lockProcess = new ReentrantLock(true);
	private final Pipe<T> pipe;
	ExternalProcessLauncher(T session, String [] messageDelimiters){
		pipe = new Pipe<T>(session,messageDelimiters);
	}


    /**
     * Main procedure of the class. Starts the external process using a new thread, then it goes sleeping until 
     * the new threads has finished its work, namely waiting for the process. Consequently, both threads mainly sleep
     * while executing the external process.
     * 
     * More in detail:
     * Let T1 be the invoking thread of this method and let T2 be the created thread:
     * T1 creates the new thread T2, starts T2 and then T1 waits until T2 confirms that the process has been started.
     * After receiving the confirmation by means of <code>cond</code> T1 starts the pipe and waits until the pipe is closed.
     * 
     * From T2's point of view: When T2 becomes alive it creates the external process and starts it. Then it informs T1 
     * that the process is running now. Afterwards it goes sleeping until it either gets interrupted or the external 
     * process has terminated. The final operation is closing the pipe.
     */
	public void launch(final String [] command,String initialMessage, PipeListener<T> listener) throws Throwable {
	     	try{
	   
	     		final ReentrantLock lock = new ReentrantLock(true);
                final Condition cond = lock.newCondition();
	     		lock.lock();
                Thread thread = new Thread(new Runnable() {
            		// This thread starts the process and waits until it has stopped.
                	@Override
                	public void run() {

                		try {   
                			lock.lock();
                			ProcessBuilder builder = new ProcessBuilder();
                			builder.command(command);
    			
                			process = builder.start();

                		} catch(IOException e){
                			throw new RuntimeException(e);
                		}
                		finally{
                			cond.signalAll();
                			lock.unlock();
                		}
                		try{
                			process.waitFor();
         
                		}catch (InterruptedException e) {/*do nothing*/}
                   		pipe.close();
                	
                	}
                });
            // start the thread and wait until the thread has started the process. Then start the pipe.
            thread.setDaemon(true);
            thread.start();
            cond.await();
            
            pipe.start(process.getInputStream(),
            	       process.getOutputStream(),
            		   process.getErrorStream(),
            		   listener);
    
            
            // send initial message: basically the smt problem.
            pipe.sendMessage(initialMessage+"\n");
  
            // wait until the pipe 
            pipe.waitForPipe();
           
	     	}finally{
	     		cleanUp();
	     	}	     			
	}
	

	/**
	 * Call this method only after the pipe has been stopped. It is not thread safe!
	 * @return
	 */
    T getCommunication(){
    	return pipe.getSession();
    }
	
	public void stop(){
	    pipe.close();
	    if(process != null){
	    	process.destroy();
	    }
	    
	}
	
	public void cleanUp(){
		try{
			lockProcess.lock();

			if(process != null) {
	 	       process.destroy();
	 	       try {
				process.getErrorStream().close();
		 	    process.getInputStream().close();
		 	    process.getOutputStream().close();
	 	       } catch (IOException e) {
	 	    	   throw new RuntimeException(e);
	 	       }
	 	       process = null;
	     }
	   }finally{
		   lockProcess.unlock();
	   }
	}	
}
