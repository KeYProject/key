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

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;


/**
 * Stores the communication between KeY and an external solver: Contains a list that stores the messages 
 * that has been sent from the solver to KeY and vice versa.
 * 
 * Further, it also contains the final result of the solver. 
 */
public class SolverCommunication {
	public static SolverCommunication EMPTY = new SolverCommunication();
			

	
	private final List<String> messages = Collections.synchronizedList(new LinkedList<String>());
	
	private SMTSolverResult finalResult = SMTSolverResult.NO_IDEA;
	private int state =0;
	private boolean resultHasBeenSet = false;
	
	private List<Throwable> exceptions = Collections.synchronizedList(new LinkedList<Throwable> ());
	
	/**
	 * The message type depends on the channel which was used for sending the message.
	 */
	public enum MessageType {Input,Output,Error}


    public static class Message{
		private final String content;
		private final MessageType type;
	
		public Message(String content, MessageType type) {
			this.content = content;
			this.type = type;
		}
		public String getContent() {
			return content;
		}	
		public MessageType getType() {
			return type;
		}
	}

	public SolverCommunication() {
	}
	

	/**
	 * Returns all messages that were sent between KeY and the solver.
	 */
	public Iterable<String> getMessages() {
		// return an new iterable object in order to guarantee that the list of messgages 
		// cannot be changed.
		return new Iterable<String>() {
			
			@Override
			public Iterator<String> iterator() {
				return messages.iterator();
			}
		};
	}
	
	/**
	 * Call this method only if you are sure that there are no other threads accessing it.
	 * It is not thread safe, but it is designed for belated analysis.
	 * @return
	 */
	public Iterable<Throwable> getExceptions() {
		return new Iterable<Throwable>() {
			
			@Override
			public Iterator<Throwable> iterator() {
				return exceptions.iterator();
			}
		};
	}
	
	public boolean exceptionHasOccurred(){
		return !exceptions.isEmpty();
	}
	
	public SMTSolverResult getFinalResult() {
		return finalResult;
	}
	
	/**
	 * Returns the current state of the communication. The states are defined by the solver classes.
	 */
	public int getState() {
		return state;
	}
	
	public boolean resultHasBeenSet() {
		return resultHasBeenSet;
	}
	
	
	/*Only public for classes of the same package */
	void setFinalResult(SMTSolverResult finalResult) {
		this.finalResult = finalResult;
		resultHasBeenSet = true;
	}


	void addMessage(String message){
		messages.add(message);
	}
	void setState(int state) {
		this.state = state;
	}
	
    void addException(Throwable e){
    	exceptions.add(e);
    }


    
    

}