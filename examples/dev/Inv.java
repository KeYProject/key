// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class Inv {
    /*@ public normal_behavior
      @requires n >= 0;
      @ensures \result==n;
      @
     @*/
    public static int test(int n) {
	int i = 0;
	/*@
	  @ loop_invariant 0<= i && i<=n;
	  @ assignable i;
	  @ decreases n-i;
	  @ */
	while (i < n) {
	    i++;
	    while (true) ;
	    
	}
	return i;
    }

    public static void main(String args[]) {
	System.out.println(test(4));
    }
}
