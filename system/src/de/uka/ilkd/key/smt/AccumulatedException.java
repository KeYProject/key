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