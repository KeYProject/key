// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.smt;

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
     * Main procedure of the class. Starts the external process, then it goes sleeping until 
     * the process has finished its work.
     */
	public void launch(final String [] command,String initialMessage, PipeListener<T> listener) throws Throwable {
		try{

			lockProcess.lock();
			try {
				ProcessBuilder builder = new ProcessBuilder();
				builder.command(command);
				process = builder.start();

				pipe.start(process.getInputStream(), process.getOutputStream(), process.getErrorStream(), listener);
			} finally {
				lockProcess.unlock();
			}
			
			// send initial message: basically the smt problem.
			pipe.sendMessage(initialMessage+"\n");
			//pipe.closeSendingPipe();
			// wait until the output has been processed
			pipe.waitForPipe();

		}finally{
			stop(); // clean up
		}	     			
	}
	

	/**
	 * Call this method only after the pipe has been stopped. It is not thread safe!
	 * @return
	 */
    T getCommunication(){
    	return pipe.getSession();
    }
	
    /**
     * Stops the external process: In particular the pipe is closed and the process is destroyed. 
     */
	public void stop(){
		lockProcess.lock();
		try {
			if(process != null){
				process.destroy();
			}
			pipe.close();
	    } finally {
			lockProcess.unlock();
		}
	}
}
