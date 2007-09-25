// @(#)$Id: JMLObjectValuePair.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

// Copyright (C) 1998, 1999 Iowa State University

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


package org.jmlspecs.models;

/** Pairs of {@link Object} and {@link JMLType}, used in the types
 * {@link JMLObjectToValueRelation} and {@link JMLObjectToValueMap}.
 *
 * <p> In a pair the first element is called the "key" and the second
 * the "value". Both the key and the value in a pair must be non-null.
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 * @author Clyde Ruby
 * @see JMLObjectToValueRelation
 * @see JMLObjectToValueMap
 */
//-@ immutable
public /*@ pure @*/ class JMLObjectValuePair implements JMLType {

    /** The key of this pair.
     */
    public final /*@ non_null @*/ Object key;

    /** The value of this pair.
     */
    public final /*@ non_null @*/ JMLType value;

    //@ public invariant owner == null;

    /*@  
      @    ensures dv != null && rv != null;
      @    signals (NullPointerException) dv == null || rv == null;
      @*/
    public JMLObjectValuePair(/*@ non_null @*/ Object dv,
                               /*@ non_null @*/ JMLType rv)
        throws NullPointerException
    {
        if (dv == null) {
            throw new NullPointerException("Attempt to create a"
                                           + " JMLObjectValuePair with null"
                                           + " key");
        }
        if (rv == null) {
            throw new NullPointerException("Attempt to create a"
                                           + " JMLObjectValuePair with null"
                                           + " value");
        }
        key = dv;
        value = (JMLType)rv.clone();
    }

    public Object clone()
    {
        return new JMLObjectValuePair(key, value);
    } 

    /*@  public normal_behavior
      @    ensures \result == (key == dv);
      @*/
    public boolean keyEquals(Object dv)
    {
        return key == dv;
    }

    /*@  public normal_behavior
      @    ensures \result == (value.equals(rv));
      @*/
    public boolean valueEquals(JMLType rv)
    {
        return value.equals(rv);
    }

    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLObjectValuePair;
      @    ensures \result == 
      @            ( ((JMLObjectValuePair)obj).key == key 
      @              && ((JMLObjectValuePair)obj).value.equals(value) );
      @ also 
      @  public normal_behavior
      @    requires obj == null || !(obj instanceof JMLObjectValuePair);
      @    ensures !\result;
      @*/
    public boolean equals(Object obj)
    {
        if (obj != null && obj instanceof JMLObjectValuePair) {
            JMLObjectValuePair pair = (JMLObjectValuePair)obj;
            return pair.key == key && pair.value.equals(value);
        }
        else {
            return false;
        }
    }

    public int hashCode() {
        return key.hashCode() + value.hashCode();
    }

    public String toString()
    {
        return(new String("(") + key + new String(", ") 
               + value + new String(")") );
    }
};

