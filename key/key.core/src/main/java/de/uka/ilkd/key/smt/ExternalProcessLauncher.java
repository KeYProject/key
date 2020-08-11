// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.smt.SolverCommunication.Message;

import java.io.IOException;
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

	private final Pipe<T> pipe;

	public ExternalProcessLauncher(T session, String[] messageDelimiters) {
		pipe = new Pipe<T>(session, messageDelimiters);
	}

    /**
     * Main procedure of the class. Starts the external process, then it goes sleeping until 
     * the process has finished its work.
	 */
	public void launch(final String [] command) throws IOException {
        try {
            ProcessBuilder builder = new ProcessBuilder(command);
            process = builder.start();

            pipe.start(process);
        } catch (Exception ex) {
            stop();
            throw ex;
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
	public void stop() {
		if(process != null){
			process.destroy();
		}
		pipe.close();
	}

	public Pipe<T> getPipe() {
		return pipe;
	}

	public void sendMessage(String message) throws IOException {
		pipe.sendMessage(message);
	}

	public Message readMessage() throws IOException, InterruptedException {
		return pipe.readMessage();
	}
}
