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
		char buf[] = new char[128];
		String message = null;
		do{
		  message = getNextMessage();
		  if(message!= null){			
			  return message;
		  }
		  try{
		    length = reader.read(buf);
		  }catch(IOException e){
			if(!Thread.currentThread().isInterrupted()){
				throw new RuntimeException(e);
			}  
		  }
		  messageBuffer = messageBuffer.append(convert(buf));
		}while(length!=-1 && !Thread.currentThread().isInterrupted());
		return message;
	}
	
	private String getNextMessage(){
		int index = -1;
		String responsibleMark = "";
		for(String mark : endOfMessage){
			int temp = messageBuffer.indexOf(mark);
			// make the message as small as possible: it may not contain delimiters.
			if(index > -1 && temp > -1){
				responsibleMark = index < temp ? responsibleMark : mark;
				index = index < temp ? index : temp;
			}else if(temp > -1){
				responsibleMark = mark;
				index = temp;
			}
			
		
		}
		if(index == -1){
			return null;
		}
		
		String message = index > 0 ? messageBuffer.substring(0, index) : null;
		messageBuffer = messageBuffer.delete(0, index+responsibleMark.length());
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
	
	public StringBuffer getMessageBuffer() {
		return messageBuffer;
	}
	
	
}
