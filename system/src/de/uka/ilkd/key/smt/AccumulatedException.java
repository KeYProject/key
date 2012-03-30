package de.uka.ilkd.key.smt;


import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.Iterator;
import java.util.LinkedList;

public class AccumulatedException extends Throwable implements Iterable<Throwable>{
	private static final long serialVersionUID = 1L;
	private final LinkedList<Throwable> exceptions = new LinkedList<Throwable>();
	
	AccumulatedException(Iterable<Throwable> exceptions){
		for(Throwable exception : exceptions){
			this.exceptions.add(exception);
		}
	} 

	@Override
	public void printStackTrace() {
		for(Throwable exception : exceptions){
			exception.printStackTrace();		}
	
		super.printStackTrace();	
	}
	
	@Override
	public void printStackTrace(PrintStream s) {
		for(Throwable exception : exceptions){
			exception.printStackTrace(s);
		}
	
		super.printStackTrace(s);
	}
	
	@Override
	public void printStackTrace(PrintWriter writer) {
		for(Throwable exception : exceptions){
			exception.printStackTrace(writer);
		}
	
		super.printStackTrace(writer);
	}

	@Override
	public Iterator<Throwable> iterator() {
		return exceptions.iterator();
	}
	
	@Override
	public String toString() {
		String s = "";
		for(Throwable exception : exceptions){
			s+= "\n"+exception.toString();
		}

		return s+"\n"+super.toString();
	}
	
}
