// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt.launcher;

/**
 * This class describes several events that can occur while 
 * executing processes.
 *
 */
public class Event {
        public enum Type  {
            /**
             * After starting the process.
             */
            PROCESS_START,   
            /**
             * After interrupting the process. 
             */
            USER_INTERRUPTION,
            /**
             * The process has been destroyed.
             */
            PROCESS_FINISHED,
            /**
             * An exception occurred.
             */
            PROCESS_EXCEPTION,
            /**
             * The process finished all of its work.
             */
            WORK_DONE,
            /**
             * Occurs periodically.
             */
            PROCESS_STATUS,
            /** The process finished a part of its work, 
             * example the external prover solved one of the given goals.*/
            PROCESS_CYCLE_FINISHED,
            /** The process was interrupted.*/
            INTERRUP_PROCESS
	};
	private ProcessLauncher launcher;
	private ProcessLaunch   launch;
	private Type		 type;
	private Object          userObject;
	private Exception 	 exception;
	public Event(ProcessLauncher l, ProcessLaunch launch, Type type){
		launcher = l;
		this.launch = launch;
		this.type = type;
	}
	
	public  Event(ProcessLauncher l, ProcessLaunch launch, Type type, Object object){
	    this(l, launch, type);
	    userObject = object;
	    
	}
	
	public  Event(ProcessLauncher l, ProcessLaunch launch, Type type, Exception exception){
	    this(l, launch, type);
	    this.exception = exception;
	    
	}

	public ProcessLauncher getLauncher() {
		return launcher;
	}


	public ProcessLaunch getLaunch() {
		return launch;
	}


	public Type getType() {
		return type;
	}
	
	public Object getUserObject(){
	    return userObject; 
	}
	
	public Exception getException(){
	    return exception;
	}

	
}
