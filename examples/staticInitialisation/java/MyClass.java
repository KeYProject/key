// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class MyClass {

    public static final int CLASS_IDENTIFIER = 4711;
    public static int COUNTER = 1;
    static {COUNTER--;}
    
    public int id = -1;


    public MyClass() {
    }

}
