// Copyright (C) 2002 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.lang;

/** JML's specification of java.lang.Integer.
 * Taken from the jmlspecs repository and modified to fit into KeY.
 * @version $Revision: 2022 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @author David R. Cok
 * @author Daniel Bruns
 */
public  /*@ pure nullable_by_default @*/ final
    class Integer /*extends Number*/ implements Comparable {

    //@ public ghost int theInteger;
    public static final int   MIN_VALUE = -2147483648;

    public static final int   MAX_VALUE = 2147483647;

    public static final Class TYPE;

    public static /*@ pure @*/ /*@ non_null @*/ String toString(int i,
                                                                  int radix);

    
    public static /*@ pure @*/ /*@ non_null @*/ String toHexString(int i);

    public static /*@ pure @*/ /*@ non_null @*/ String toOctalString(int i);

    public static /*@ pure @*/ /*@ non_null @*/ String toBinaryString(int i);
            

    public static /*@ pure @*/ int parseInt(String s, int radix)
        throws NumberFormatException;
                

    public static /*@ pure @*/ int parseInt(String s)
        throws NumberFormatException;

    public static /*@ pure @*/ /*@ non_null @*/
        Integer valueOf(String s, int radix)
        throws NumberFormatException;
    
    public static /*@ pure @*/ /*@ non_null @*/ Integer valueOf(String s)
        throws NumberFormatException;

    /*@ public normal_behavior
      @   ensures theInteger == value;
      @*/
    //@ pure
    public Integer(int value);
    
    //@ pure
    public Integer(String s) throws NumberFormatException ;
 
    /*@ also
      @   public normal_behavior
      @     ensures \result == (byte) theInteger;
      @*/
    //@ pure
    public byte byteValue();
    
    /*@ 
      @   public normal_behavior
      @     ensures \result == (short) theInteger;
      @*/
    public /*@ pure @*/ short shortValue();

    /*@ 
      @   public normal_behavior
      @     ensures \result == theInteger;
      @*/
    public /*@ pure @*/ int intValue();
    
    /*@ 
      @   public normal_behavior
      @     ensures \result == (long) theInteger;
      @*/
    public /*@ pure @*/ long longValue();
    
    public /*@ non_null @*/ String toString();
            
    /*@ 
      @   public normal_behavior
      @     ensures \result == theInteger;
      @*/
    public int hashCode();

    /*@ also
      @   public normal_behavior
      @     requires obj != null && (obj instanceof Integer);
      @     ensures \result <==> intValue() == ((Integer)obj).intValue();
      @   also
      @   public normal_behavior
      @     requires obj == null || !(obj instanceof Integer);
      @     ensures !\result;
      @*/
    public boolean equals(/*@nullable*/Object obj);
  
    public static /*@ pure @*/
        Integer getInteger(String nm);

    public static /*@ pure @*/ 
        Integer getInteger(String nm, int val);

    public static /*@ pure @*/ 
        Integer getInteger(String nm, Integer val);
    
    public static /*@ pure @*/ /*@ non_null @*/
        Integer decode(/*@ non_null @*/ String nm)
        throws NumberFormatException;

    /*@ public normal_behavior
      @ requires anotherInteger != null;
      @ {|
      @   requires theInteger == anotherInteger.intValue();
      @   ensures \result == 0;
      @ also 
      @   requires theInteger < anotherInteger.intValue();
      @   ensures \result == -1;
      @ also
      @   requires theInteger > anotherInteger.intValue();
      @   ensures \result == 1;
      @ |}
      @ also public exceptional_behavior
      @   requires anotherInteger == null;
      @   signals_only NullPointerException;
      @*/
    public int compareTo(Integer anotherInteger);
            
    /*@ also
      @   public normal_behavior
      @     requires o != null && (o instanceof Integer);
      @     ensures \result == compareTo((Integer) o);
      @ also
      @   public exceptional_behavior
      @     requires o != null && !(o instanceof Integer);
      @     signals_only ClassCastException;
      @ also public exceptional_behavior
      @   requires o == null;
      @   signals_only NullPointerException;
      @*/
    public int compareTo(Object o);

}
