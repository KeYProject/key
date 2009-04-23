// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class CubicSum {

    /*@ public normal_behavior
     @ requires n >= 0;
     @ ensures 4 * \result == n*n * (n+1)*(n+1);
     @ diverges true;
     @*/
    public static int cubicSum(int n) {
	int i = 0;
	int res = 0;
	/*@
	  @ loop_invariant 0<= i && i<=n && 4 * res == i*i * (i+1)*(i+1);
	  @ assignable i,res;
	  @ */
	while (i < n) {
	    i++;
	    res += i*i*i;
	}
	return res;
    }
}
