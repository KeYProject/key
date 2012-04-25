package de.uka.ilkd.key.smt;


import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.LinkedList;
import java.util.List;
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
	private final ReentrantLock listenerLock = new ReentrantLock(true);
	private final LinkedList<PipeListener<T>> listeners = new LinkedList<PipeListener<T>>();
	
	/** there are three worker threads, thus three permits are acquired in advance. After a worker thread
	 * has done its work it releases one permit. Thus, the semaphore has exactly one permit when all worker
	 * have finished their work.*/
	private final Semaphore     stopWaiting = new Semaphore(-2);

	/**
	 * The workers of the pipe. One worker is responsible for sending messages, while the other two workers
	 * handle messages which are received. 
	 */
	private List<Worker>  workers = new LinkedList<Worker>();
	private final ReentrantLock workerLock   = new ReentrantLock(true);
	/**
	 * Stores messages that are to be sent in the next cycle of the worker responsible for sending messages.
	 */
	private LinkedList<String> queue = new LinkedList<String>();
	private final ReentrantLock queueLock = new ReentrantLock(true);
	
	/**The sender goes to sleep when there are no messages to be sent. If you want to wake him up, use this
	 * condition. */
	private final Condition     postMessages = queueLock.newCondition();
	
	/**
	 * External threads can wait until the pipe is closed. The condition <code>await</code> is used for that purpose,
	 * see <code>waitForPipe</code>.
	 */
	private final ReentrantLock awaitLock    = new ReentrantLock(true);
	private final Condition     awaitCond    = awaitLock.newCondition();
	
	/**
	 * The delimiters of the messages, i.e. strings that indicate the end of a message. If you specify several
	 * delimiters a single message is chosen as small as possible, i.e., it does not contain any delimiter. 
	 */
	private final String []     messageDelimiters;
	
	public  static final int NORMAL_MESSAGE = 0;
	public  static final int ERROR_MESSAGE =1;
	
	/**
	 * User specific data.
	 */
	private final T session;
	
    
	
	public Pipe(T session, String [] messageDelimiters) {
		super();
		this.session = session;
		this.messageDelimiters = messageDelimiters;
	}
	
	/**
	 * Worker class for both the receiver and sender of the pipe. Is mainly responsible for starting both types of
	 * workers.
	 */
	private abstract class Worker extends Thread{


		
		
		public Worker(String name) {
			super();
			this.setName(name);
			this.setDaemon(true);
		}

		@Override
		public void run() {
			try{
				doWork();
			}catch(Throwable e){
				try{
					listenerLock.lock();
					e.printStackTrace();
					close();
					for(PipeListener<T> listener : listeners){
						listener.exceptionOccurred(Pipe.this,e);
					}
				}finally{
					listenerLock.unlock();
				}
			}finally{
				// the work is done, unregister from the system. 
				stopWaiting.release();
				try{
					awaitLock.lock();
					awaitCond.signalAll();
				}finally{
					awaitLock.unlock();
				}
			}
		}
		
		abstract protected void doWork();
		abstract protected void stopWorking() throws IOException;
	}

	/**
	 * Mainly consists of a queue for messages. Each time the queue is filled with a message, the worker removes
	 * the message from the queue and sends it to the other side of the pipe. 
	 */
	private class Sender extends Worker{
		public Sender(OutputStream output, String name) {
			super(name);
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
						writer.write(message+"\n");
						writer.flush();
					}
			   		postMessages.await(); // save against spurious wakeups because it is placed in a loop.
	    		} catch (InterruptedException e) {
					// set interruption flag. 
					Thread.currentThread().interrupt();

				  }
				  catch (IOException e) {
					  close();
					  throw new RuntimeException(e);
				}
			}
	
		}


		@Override
		protected void stopWorking() throws IOException {
			this.interrupt();
			output.close();
			
		}		
	}
	

	/**
	 * Waits until a message is received from the other side of the pipe. Then it forwards the message to its
	 * listeners and waits again until the next message is received.
	 */
	private class Receiver extends Worker{
		private final InputStream input;
		private final int type;
		
		public Receiver(InputStream input, int type, String name) {
			super(name);
			this.input = input;
			this.type = type;
		}


		
		protected void doWork(){
			// do not use BufferedReader directly, but this wrapper in order to support different
			// message delimiters.
			BufferedMessageReader reader = new BufferedMessageReader(
													new InputStreamReader(input),
													messageDelimiters); 
			String message = null;
			 do{
				message = null;
				try {
					//the next call blocks the thread and waits until there is a message. 
 					message = reader.readMessage();
				} catch (Throwable e) {
					close();
					// only throw an exception if the thread has not been interrupted. It can be that
					// the exception comes from the interruption.
					if(!Thread.currentThread().isInterrupted()){
						throw new RuntimeException(e);
					}
				}					 
				if(message != null){
					deliverMessage(message);
				}
			 }while(message != null && !Thread.currentThread().isInterrupted());
			  // process last remaining input:
			  StringBuffer buf = reader.getMessageBuffer();
			  if(buf.length()>0){
				  deliverMessage(buf.toString());
			  }
			
		}
		
		
		private void deliverMessage(String message){
			try{
				listenerLock.lock();
				for(PipeListener<T> listener : listeners){
					listener.messageIncoming(Pipe.this,message, type);
				}
			}finally{
				listenerLock.unlock();
			}
		}



		@Override
		protected void stopWorking() throws IOException {
			this.interrupt();
		    input.close();
			
		}
	}

	public void start(InputStream input, OutputStream output,InputStream error, PipeListener<T> listener){
		addListener(listener);
		try{
			workerLock.lock();
			workers.add(new Receiver(input,NORMAL_MESSAGE,"receiver for normal messages"));
			workers.add(new Sender(output,"sender"));
			workers.add(new Receiver(error,ERROR_MESSAGE,"receiver for error messages"));
			
	
			for(Thread thread : workers){
				thread.setDaemon(true);
				thread.start();
			}
		}finally{
			workerLock.unlock();
		}
		
	}
	
	
	public void close(){
		try{
			workerLock.lock();
			for(Worker worker : workers){
				try{
				worker.stopWorking();
				}catch(Throwable e){
					throw new RuntimeException(e);
				}
			}
			
		}finally{
			workerLock.unlock();
		}
	}
	

	
	/**
	 * sends a message to the external process. Mainly it adds a new message to
	 * the message queue and wakes up the sender.
	 */
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
				close(); // stop pipe and wait until all worker have stopped.				
			}
		}
	}


}
