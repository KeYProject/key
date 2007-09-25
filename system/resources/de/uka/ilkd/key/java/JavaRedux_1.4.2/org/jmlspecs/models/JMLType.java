// @(#)$Id: JMLType.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

// Copyright (C) 1998, 1999, 2002 Iowa State University

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

/** Objects with a clone and equals method.
 * JMLObjectType and JMLValueType are refinements
 * for object and value containers (respectively).
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLObjectType
 * @see JMLValueType
 */
//-@ immutable
//@ pure
public interface JMLType extends Cloneable, java.io.Serializable {

    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null;
      @     ensures \result instanceof JMLType;
      @     ensures \result.equals(this);
      @*/
    /*@    ensures \result != null
      @        && \typeof(\result) <: \type(JMLType);
      @*/
    public /*@ pure @*/ Object clone();    

    /** Test whether this object's value is equal to the given argument.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result ==>
      @             ob2 != null
      @             && (* ob2 is not distinguishable from this,
      @                   except by using mutation or == *);
      @   public normal_behavior
      @   {|
      @      requires ob2 != null && ob2 instanceof JMLType;
      @      ensures ((JMLType)ob2).equals(this) == \result;
      @    also
      @      requires ob2 == this;
      @      ensures \result <==> true;
      @   |}
      @*/
    public /*@ pure @*/ boolean equals(Object ob2);    

    /** Return a hash code for this object.
     */
    public /*@ pure @*/ int hashCode();
}
