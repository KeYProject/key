// @(#)$Id: JMLEqualsEqualsPair.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

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

/** Pairs of {@link Object} and {@link Object}, used in the types
 * {@link JMLEqualsToEqualsRelation} and {@link JMLEqualsToEqualsMap}.
 *
 * <p> In a pair the first element is called the "key" and the second
 * the "value". Both the key and the value in a pair must be non-null.
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 * @author Clyde Ruby
 * @see JMLEqualsToEqualsRelation
 * @see JMLEqualsToEqualsMap
 */
//-@ immutable
public /*@ pure @*/ class JMLEqualsEqualsPair implements JMLType {

    /** The key of this pair.
     */
    public final /*@ non_null @*/ Object key;

    /** The value of this pair.
     */
    public final /*@ non_null @*/ Object value;

    //@ public invariant owner == null;

    /*@  public model_program {
      @    assume dv != null && rv != null;
      @    set owner = null;
      @    key = dv;
      @    value = rv;
      @  }
      @ also
      @    ensures dv != null && rv != null;
      @    signals (NullPointerException) dv == null || rv == null;
      @*/
    /** Initialize the key and value of this pair.
     */
    public JMLEqualsEqualsPair(/*@ non_null @*/ Object dv,
                               /*@ non_null @*/ Object rv)
        throws NullPointerException
    {
        if (dv == null) {
            throw new NullPointerException("Attempt to create a"
                                           + " JMLEqualsEqualsPair with null"
                                           + " key");
        }
        if (rv == null) {
            throw new NullPointerException("Attempt to create a"
                                           + " JMLEqualsEqualsPair with null"
                                           + " value");
        }
        //@ assume dv != null && rv != null;
        //@ set owner = null;
        key = dv;
        value = rv;
    }

    // inherit javadoc comment
    /*@ also
      @  public model_program {
      @    return new JMLEqualsEqualsPair(key, value);
      @  }
      @*/
    public Object clone()
    {
        return new JMLEqualsEqualsPair(key, value);
    } //@ nowarn Post;

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
    public boolean valueEquals(Object rv)
    {
        return value.equals(rv);
    }

    /** Test whether this object's value is equal to the given argument.
     * @see #keyEquals
     */
    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLEqualsEqualsPair;
      @    ensures \result == 
      @            ( ((JMLEqualsEqualsPair)obj).key.equals(key) 
      @              && ((JMLEqualsEqualsPair)obj).value.equals(value) );
      @ also 
      @  public normal_behavior
      @    requires obj == null || !(obj instanceof JMLEqualsEqualsPair);
      @    ensures !\result;
      @*/
    public boolean equals(Object obj)
    {
        if (obj != null && obj instanceof JMLEqualsEqualsPair) {
            JMLEqualsEqualsPair pair = (JMLEqualsEqualsPair)obj;
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
    /*@ also
      @  public normal_behavior
      @    ensures (* \result is a string that starts with a '(' followed by
      @                the strings representing key and value separated by
      @                a comma and ends with a ')' 
      @              *);
      @ for_example
      @   public normal_example
      @     requires (* key is 4 and value is 2 *);
      @     ensures (*  \result is the string "(4, 2)"  *);
      @*/
    public String toString()
    {
        return(new String("(") + key + new String(", ") 
               + value + new String(")") );
    }
};

