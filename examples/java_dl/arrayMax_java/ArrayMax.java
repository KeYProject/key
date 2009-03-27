// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.


public class ArrayMax {
    
    /*@
      @ public normal_behavior
      @ requires a != null;
      @ ensures (\forall int j; j >= 0 && j < a.length;
      @                         \result >= a[j]);
      @ ensures a.length > 0 ==>
      @         (\exists int j; j >= 0 && j < a.length;
      @                         \result == a[j]);
      @*/
    public static /*@ pure @*/ int max(int[] a) {
	if ( a.length == 0 ) return 0;
	int max = a[0], i = 1;
	/*@
	  @ loop_invariant
	  @      i <= a.length
	  @      &&
	  @      (\forall int j; j >= 0 && j < i; max >= a[j])
	  @      &&
	  @      (\exists int j; j >= 0 && j < i; max == a[j]);
	  @ modifies i, max;
	  @ decreases a.length - i;
	  @*/
	while ( i < a.length ) {
	    if ( a[i] > max ) max = a[i];
	    ++i;
	}
	return max;
    }

}
