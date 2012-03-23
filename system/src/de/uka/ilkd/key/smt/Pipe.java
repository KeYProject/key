package de.uka.ilkd.key.smt;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.LinkedList;
import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

interface PipeListener{
	/** Is called when a message from the other side of the pipe is received. 
	 * @param message
	 */
	void messageIncoming(Pipe pipe, String message, int type);
}

/**
 * On each side of the pipe there are sender and receivers:
 ***** Receiver ====<=Output======= Sender    ******************
 *KeY* Sender	======Input=>====== Receiver  *External Process*
 ***** Receiver ====<=Error======== Sender    ******************
 * 
 */
class Pipe{

	private final LinkedList<PipeListener> listeners = new LinkedList<PipeListener>();
	private final Semaphore     stopProcesses = new Semaphore(0);
	private Thread [] threads = new Thread[0];
	private LinkedList<String> queue = new LinkedList<String>();
	private final ReentrantLock queueLock = new ReentrantLock(true);
	private final ReentrantLock listenerLock = new ReentrantLock(true);
	private final Condition     postMessages = queueLock.newCondition();
	public  final int NORMAL_MESSAGE = 0;
	public  final int ERROR_MESSAGE =1;

	
	private class Sender implements Runnable{
		public Sender(OutputStream output) {
			super();
			this.output = output;
		}
		private final OutputStream output;


		@Override
		public void run() {
			queueLock.lock();
		    OutputStreamWriter writer = new OutputStreamWriter(output);
			while(!stopProcesses.tryAcquire()){
				try {
					System.out.println("Await message");
					postMessages.await();
					while(!queue.isEmpty()){
						String message = queue.pop();
						System.out.println("Send message: "+ message);
						writer.write(message);
						writer.flush();
					}
				} catch (InterruptedException e) {/*Do nothing*/}
				  catch (IOException e) {
					  stop();
					  throw new RuntimeException(e);
				}
			}
		}		
	}
	
	public void stop(){
		for(Thread thread : threads){
			thread.interrupt();
		}
		stopProcesses.release(threads.length);
	}
	
	private class Receiver implements Runnable{
		private final InputStream input;
		private final int type;
		
		public Receiver(InputStream input, int type) {
			super();
			this.input = input;
			this.type = type;
		}

		@Override
		public void run() {
			 BufferedReader reader = new BufferedReader(new InputStreamReader(input));
			 String message = null;
			 do{
				message = null;
				 try {
					message = reader.readLine();
				} catch (IOException e) {
					stop();
					new RuntimeException(e);
				}
				if(message != null){
					try{
						listenerLock.lock();
						for(PipeListener listener : listeners){
							listener.messageIncoming(Pipe.this, message, type);
						}
					}finally{
						listenerLock.unlock();
					}
				}
			 }while(message != null);			
		}		
	}

	public void start(InputStream input, OutputStream output,InputStream error){
		threads = new Thread[] {
			new Thread(new Receiver(input,NORMAL_MESSAGE)),
			new Thread(new Sender(output)),
			new Thread(new Receiver(error,ERROR_MESSAGE))
		};
		for(Thread thread : threads){
			thread.setDaemon(true);
			thread.start();
		}
	}
	
	
	
	void sendMessgage(String message){
		try{
			queueLock.lock();
			queue.add(message);
	
		}
		finally{
			postMessages.signalAll();
			queueLock.unlock();
		
		}
	}
	
	void addListener(PipeListener listener){
		try{
			listenerLock.lock();
			listeners.add(listener);
		}finally{
			listenerLock.unlock();
		}
	}

}
