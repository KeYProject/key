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

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

public class ExternalProcessLauncher<T> {
    	public final static int RESULT = 0;
    	public final static int ERROR  = 1;
    	public final static int EXIT_CODE = 2;
        private Process process;
        private ReentrantLock lockProcess = new ReentrantLock(true);
        private final Pipe<T> pipe;
        ExternalProcessLauncher(T session){
        	pipe = new Pipe<T>(session);
        }


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
                			
                			//builder.command("/home/benjamin/programs/simplify/test","-nosc");
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
                		System.out.println("Process finish");
                		pipe.stop();
                	
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
	    pipe.stop();
	}
	
	public void cleanUp(){
		try{
			lockProcess.lock();
			System.out.println("CLEAN UP");
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
	
	    /** Read the input until end of file and return contents in a
	     * single string containing all line breaks. */
	    static String read(InputStream in) throws IOException {
		BufferedReader reader = new BufferedReader(new InputStreamReader(in));
		StringBuffer sb = new StringBuffer();

		int x = reader.read();
		while (x > -1) {
		    sb.append((char) x);
		    x = reader.read();
		}
		return sb.toString();
	    }

	
}
