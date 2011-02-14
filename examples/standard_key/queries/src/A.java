// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class A {


    public int query(int m) {
	int i = 100000;	
	while (i>0) {
	    // compute something very difficult
	    i--; 
	}
	return i + m;
    }

}
