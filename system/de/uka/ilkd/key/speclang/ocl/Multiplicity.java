// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl;

import java.util.StringTokenizer;



public class Multiplicity {

    public static int INFINITE = -10;

    public static Multiplicity STANDARD     = new Multiplicity(1,1);
    public static Multiplicity ZERO_TO_INF  = new Multiplicity(0,INFINITE);
    public static Multiplicity ONE_TO_INF   = new Multiplicity(1,INFINITE);
    public static Multiplicity ZERO_OR_ONE  = new Multiplicity(0,1);


    protected int min, max;

    public Multiplicity(int min, int max) {
	if ( min<0 )
	    throw new IllegalArgumentException("minimum multiplicity must be at least 0, is "+min);
	if ( max==0 )
	    throw new IllegalArgumentException("maximum multiplicity must not be 0");
	if ( !(min<=max  || max==INFINITE))
	    throw new IllegalArgumentException(
					       "minimum multiplicity ("+min+") must not be greater than maximum multiplicity ("+max+")"
					       );
	this.min=min;
	this.max=max;
    }

    public int getMax() {
	return max;
    }

    public int getMin() {
	return min;
    }

    public static Multiplicity getMultiplicityFromString(String s) {
	if (s.equals("0..*") || 
	    s.equals("*")){
	    return Multiplicity.ZERO_TO_INF;
	} else if (s.equals("1..*")){
	    return Multiplicity.ONE_TO_INF;
	} else if (s.equals("1")){
	    return Multiplicity.STANDARD;
	} else if (s.equals("0..1")){
	    return Multiplicity.ZERO_OR_ONE;
	} else {    
	     StringTokenizer st = new StringTokenizer(s, "..");
             
             if (st.countTokens()>0 || st.countTokens()<=2){
                 int[] boundaries = new int[st.countTokens()]; 
                 int count = 0;
                 while (st.hasMoreTokens()) {
                     int nr;             
                     try {
                         nr = Integer.parseInt(st.nextToken());             
                     } catch (NumberFormatException nfe) {
                         //not a number
                         return null;
                     }
                     boundaries[count]=nr;
                     count++;
                 }                 
                 final int min1 = boundaries[0];
                 final int max1 = count > 1 ? boundaries[1] : boundaries[0];
                 return new Multiplicity(min1, max1);
             }
        }
	return null;
    }

    public String toString() {
	if (max==-10)	    
	    return ""+min+"..*";
	else
	    return ""+min+".."+max;
    }

}

