// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class A {
    
    private int a() {
	return 1;
    }

    public int mInA() {
	return a();
    }


  
    private int a2(byte a) {
	return 1;
    }

    public int a2(int a) {
	return 2;
    }

    public int m2InA() {
	return a2((byte)2);
    }

}
