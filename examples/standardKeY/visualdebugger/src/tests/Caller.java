// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package tests;

/**
 * The Class Caller.
 */
public class Caller {
	
    private/* @ spec_public @ */int i;
	
	public  Caller(){
		i=0;		
	}
	
	/**
	 * Calling function.
	 * 
	 * This function may cause a class cast exception
	 * 						  or nullpointer exception
	 * @param o the object
	 * 
	 * @return the int
	 */

		/*@ public normal_behavior
		 ensures true; @*/
	
	public int callingFunction(Object o) {

		// if(o!=null)
	//		 i++;
		i = ((ClassA2)o).myFunction();
		return i;
	}
}
