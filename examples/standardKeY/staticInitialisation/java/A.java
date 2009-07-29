// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class A {

    public static int ATTR_A1;
    public static int ATTR_A2;
    static {
	ATTR_A1 = 3;
    }

    final static int CONSTANT = 3;    


    public static FailedStaticInit SAVE;
    
    public static void methA() {	
    }

    public A() {
    }
    
    
}
