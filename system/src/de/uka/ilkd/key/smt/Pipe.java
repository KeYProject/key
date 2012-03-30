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

interface PipeListener<T>{
	/** Is called when a message from the other side of the pipe is received. 
	 * @param message
	 */
	void messageIncoming(Pipe<T> pipe, String message, int type);
	void exceptionOccurred(Pipe<T> pipe,Throwable exception);

}

/**
 * On each side of the pipe there are sender and receivers:
 ***** Receiver ====<=Output======= Sender    ******************
 *KeY* Sender	======Input=>====== Receiver  *External Process*
 ***** Receiver ====<=Error======== Sender    ******************
 * 
 */
class Pipe<T>{

	private final LinkedList<PipeListener<T>> listeners = new LinkedList<PipeListener<T>>();
	private final Semaphore     stopWaiting = new Semaphore(0);

	private Thread [] threads = new Thread[0];
	private LinkedList<String> queue = new LinkedList<String>();
	private final ReentrantLock queueLock = new ReentrantLock(true);
	private final ReentrantLock listenerLock = new ReentrantLock(true);
	private final Condition     postMessages = queueLock.newCondition();
	private final ReentrantLock awaitLock    = new ReentrantLock(true);
	private final Condition     awaitCond    = awaitLock.newCondition();
	private final ReentrantLock threadLock   = new ReentrantLock(true);
	
	public  static final int NORMAL_MESSAGE = 0;
	public  static final int ERROR_MESSAGE =1;
	private final T session;
	
    
	
	public Pipe(T session) {
		super();
		this.session = session;
	}
	
	/**
	 * Worker class for both the receiver and sender of the pipe. Is mainly responsible for starting both types of
	 * workers.
	 */
	private abstract class Worker implements Runnable{
		@Override
		public void run() {
			try{
				doWork();
			}catch(Throwable e){
				try{
					listenerLock.lock();
					e.printStackTrace();
					System.out.println("Stop called by listener");
					stop();
					for(PipeListener<T> listener : listeners){
						listener.exceptionOccurred(Pipe.this,e);
					}
				}finally{
					listenerLock.unlock();
				}
			}
		}
		
		abstract protected void doWork();
	}

	/**
	 * Mainly consists of a queue for messages. Each time the queue is filled with a message, the worker removes
	 * the message from the queue and sends it to the other side of the pipe. 
	 */
	private class Sender extends Worker{
		public Sender(OutputStream output) {
			super();
			this.output = output;
		}
		private final OutputStream output;


		protected void doWork() {
			queueLock.lock();
		    OutputStreamWriter writer = new OutputStreamWriter(output);
			while(!Thread.interrupted()){
				try {					
					while(!queue.isEmpty()){
						String message = queue.pop();
						System.out.println("Send message: "+ message);
						writer.write(message+"\n");
						writer.flush();
					}
			   		postMessages.await(); // save against spurious wakeups because it is placed in a loop.
	    		} catch (InterruptedException e) {
					// set interruption flag. 
					Thread.currentThread().interrupt();

				  }
				  catch (IOException e) {
					  stop();
					  throw new RuntimeException(e);
				}
			}
			System.out.println("FINISH: Sender");
		}		
	}
	

	/**
	 * Waits until a message is received from the other side of the pipe. Then it forwards the message to its
	 * listeners and waits again until the next message is received.
	 */
	private class Receiver extends Worker{
		private final InputStream input;
		private final int type;
		
		public Receiver(InputStream input, int type) {
			super();
			this.input = input;
			this.type = type;
		}


		
		protected void doWork(){
			 BufferedReader reader = new BufferedReader(new InputStreamReader(input));
			 String message = null;
			 do{
				message = null;
				 try {
					 System.out.println("Wait for incoming message");
					char buf[] = new char[256];
					reader.read(buf);
				//	System.out.println(buf);
					//message = new String(buf);
			
 					message = reader.readLine();
 					System.out.println("Message has been read");
				} catch (IOException e) {
					stop();
					throw new RuntimeException(e);
				}
				if(message != null){
					try{
						listenerLock.lock();

						for(PipeListener<T> listener : listeners){
							listener.messageIncoming(Pipe.this, message, type);
						}
					}finally{
						listenerLock.unlock();
					}
				}
			 }while(message != null && !Thread.interrupted());	
		}
	}

	public void start(InputStream input, OutputStream output,InputStream error, PipeListener<T> listener){
		addListener(listener);
		try{
			threadLock.lock();

			threads = new Thread[] {
					new Thread(new Receiver(input,NORMAL_MESSAGE)),
					new Thread(new Sender(output)),
					new Thread(new Receiver(error,ERROR_MESSAGE))
			};
			for(Thread thread : threads){
				thread.setDaemon(true);
				thread.start();
			}
		}finally{
			threadLock.unlock();
		}
		
	}
	
	
	public void stop(){
		System.out.println("STOP");
		try{
			threadLock.lock();
			for(Thread thread : threads){
				thread.interrupt();
			}
		}finally{
			threadLock.unlock();
		}
		
		// release lock for thread waiting by waitForPipe():
		stopWaiting.release(1);
		// signal the receivers to wake up:
		try{
			awaitLock.lock();
			awaitCond.signalAll();
		}finally{
			awaitLock.unlock();
		}
		System.out.println("STOPPED");
	}
	

	
	
	void sendMessage(String message){
		try{
			queueLock.lock();
			queue.add(message);
	
		}
		finally{
			postMessages.signalAll();
			queueLock.unlock();
		
		}
	}
	
	void addListener(PipeListener<T> listener){
		try{
			listenerLock.lock();
			listeners.add(listener);
		}finally{
			listenerLock.unlock();
		}
	}
	
	public T getSession() {
		return session;
	}
	
	public void waitForPipe(){
		awaitLock.lock();
		while(!stopWaiting.tryAcquire()){ // loop protects for spurious wakeup
			try {
			  awaitCond.await();
			} catch (InterruptedException e) {
				break; // stop waiting.
			}
		}
	}


}
