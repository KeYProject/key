// @(#)$Id: JMLEqualsValuePair.java 1.1.1.1 Mon, 09 May 2005 15:27:50 +0200 engelc $

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
 * {@link JMLEqualsToValueRelation} and {@link JMLEqualsToValueMap}.
 *
 * <p> In a pair the first element is called the "key" and the second
 * the "value". Both the key and the value in a pair must be non-null.
 *
 * @version $Revision: 1.1.1.1 $
 * @author Gary T. Leavens
 * @author Clyde Ruby
 * @see JMLEqualsToValueRelation
 * @see JMLEqualsToValueMap
 */
//-@ immutable
public /*@ pure @*/ class JMLEqualsValuePair implements JMLType {

    /** The key of this pair.
     */
    public final /*@ non_null @*/ Object key;

    /** The value of this pair.
     */
    public final /*@ non_null @*/ JMLType value;

    //@ public invariant owner == null;

    /*@  also
      @    ensures dv != null && rv != null;
      @    signals (NullPointerException) dv == null || rv == null;
      @*/
    /** Initialize the key and value of this pair.
     */
    public JMLEqualsValuePair(/*@ non_null @*/ Object dv,
                               /*@ non_null @*/ JMLType rv)
        throws NullPointerException
    {
        if (dv == null) {
            throw new NullPointerException("Attempt to create a"
                                           + " JMLEqualsValuePair with null"
                                           + " key");
        }
        if (rv == null) {
            throw new NullPointerException("Attempt to create a"
                                           + " JMLEqualsValuePair with null"
                                           + " value");
        }
        key = dv;
        value = (JMLType)rv.clone();
    }

    // inherit javadoc comment
    /*@ also
      @  public model_program {
      @    return new JMLEqualsValuePair(key, value);
      @  }
      @*/
    public Object clone()
    {
        return new JMLEqualsValuePair(key, value);
    } 

    /** Tell whether this object's key is equal to the given key.
     * @see #equals
     */
    /*@  public normal_behavior
      @    ensures \result == (key.equals(dv));
      @*/
    public boolean keyEquals(Object dv)
    {
        return key.equals(dv);
    }

    /** Tell whether this object's key is equal to the given key.
     * @see #equals
     */
    /*@  public normal_behavior
      @    ensures \result == (value.equals(rv));
      @*/
    public boolean valueEquals(JMLType rv)
    {
        return value.equals(rv);
    }

    /** Test whether this object's value is equal to the given argument.
     * @see #keyEquals
     */
    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLEqualsValuePair;
      @    ensures \result == 
      @            ( ((JMLEqualsValuePair)obj).key.equals(key) 
      @              && ((JMLEqualsValuePair)obj).value.equals(value) );
      @ also 
      @  public normal_behavior
      @    requires obj == null || !(obj instanceof JMLEqualsValuePair);
      @    ensures !\result;
      @*/
    public boolean equals(Object obj)
    {
        if (obj != null && obj instanceof JMLEqualsValuePair) {
            JMLEqualsValuePair pair = (JMLEqualsValuePair)obj;
            return pair.key.equals(key) && pair.value.equals(value);
        }
        else {
            return false;
        }
    }

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return key.hashCode() + value.hashCode();
    }

    /** Return a string representation of this object.
     */
    public String toString()
    {
        return(new String("(") + key + new String(", ") 
               + value + new String(")") );
    }
};

