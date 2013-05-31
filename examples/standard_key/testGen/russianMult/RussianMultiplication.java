// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

public class RussianMultiplication{

    /*@ public normal_behavior
      @  requires a<Integer.MAX_VALUE && (a!=0 ==> b<=Integer.MAX_VALUE/a);
      @  requires a>Integer.MIN_VALUE && (a!=0 ==> b>=Integer.MIN_VALUE/a);
      @  ensures \result == a*b;
      @*/
    public int russianMultiplication(int a, int b){
        int z = 0;
	//This is not valid JML
	/*@ //maintaining \old(a)*\old(b)==z+a*b;
	  @ //post \old(a)*\old(b) == z;
	  @ //assignable a,b;
	  @*/
        while(a != 0){
            if(a%2 != 0){
                z = z+b;
            }
            a = a/2;
            b = b*2;
        }
        return z;
    }
    
}
