// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package tests;

public class Main {

	/**
	 * @param args
	 */
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures true;
	  @ */
	public static void main(String[] args) {
		ClassA2 a2 = new ClassA2();
		Caller c = new Caller();
		// null instead of a2 cause exception
		System.out.println( c.callingFunction(a2));		

	}

}
