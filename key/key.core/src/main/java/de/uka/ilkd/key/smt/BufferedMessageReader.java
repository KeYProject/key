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

import java.io.IOException;
import java.io.InputStreamReader;


/**
 * Wraps BufferedReader in order to provide different message delimiters.
 */
public class BufferedMessageReader {
	final InputStreamReader reader;
	StringBuffer messageBuffer = new StringBuffer();
	final String [] endOfMessage;

	public BufferedMessageReader(InputStreamReader reader, String [] endOfMessage) {
		super();
		this.reader = reader;
		this.endOfMessage = endOfMessage;
	}
	

	/**
	 * Call this method in order to read the next message from the given input stream. If there is no message,
	 * it blocks until there is a further message or the stream has been closed.	
	 */
	public String readMessage() {
		int length = -1;
		
		String message = null;
		do{
		  do {
			message = getNextMessage();
		  } while (message != null && message.length() == 0); // ignore empty messages (can occur with Z3 on windows due to \r\n line ending)
		  if (message != null){
			  //System.out.println("Extracted a message with length " + message.length() + ", remaining buffer: " + messageBuffer.length());
			  return message;
		  }
		  char buf[] = new char[128]; // create new buffer in every loop cycle!
		  try{
		    length = reader.read(buf);
		  }catch(IOException e){
			if(!Thread.currentThread().isInterrupted()){
				throw new RuntimeException(e);
			}  
		  }
		  messageBuffer = messageBuffer.append(convert(buf));
		  //System.out.println("Read " + length + " bytes; new buffer: " + messageBuffer.length());
		}while(length!=-1 && !Thread.currentThread().isInterrupted());
		return message;
	}
	
	private String getNextMessage(){
		int index = -1;
		String responsibleMark = "";
		for(String mark : endOfMessage){
			int temp = messageBuffer.indexOf(mark);
			// make the message as small as possible: it may not contain delimiters.
			if(temp > -1 && (index < 0 || temp < index)){
				responsibleMark = mark;
				index = temp;
			}
			
		
		}
		if(index == -1){
			return null;
		}
		String message = index >= 0 ? messageBuffer.substring(0, index) : null;
		messageBuffer = new StringBuffer(messageBuffer.substring( index+responsibleMark.length()));
		return message;
	}
	
	private String convert(char [] buf){
		String result ="";
		for(int i=0; i  <buf.length; i++){
			if(buf[i]==0){
				break;
			}
			result += buf[i];
		}
		return result;
	}
	
	/**
	 * Returns the currently message buffer encoded by a string.
	 */
	public StringBuffer getMessageBuffer() {
		return messageBuffer;
	}
	
	
}