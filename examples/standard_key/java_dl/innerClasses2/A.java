// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class A{

    public int i=0;

    class InnerA{
	
	/*@ public normal_behavior
	  @  ensures \result==A.this.i;
	  @*/
	public int m(){
	    return i;
	}

    }

}
