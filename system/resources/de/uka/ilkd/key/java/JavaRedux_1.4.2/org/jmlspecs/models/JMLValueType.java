// @(#)$Id: JMLValueType.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

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
                                                                              
/** Objects that contain values.
 * It is the intention that classes that implement JMLValueType provide a
 * "value semantics" for both clone() and equal(). Equality must be defined
 * by the ".equals()" for any objects contained within an instance of the
 * class. clone() must use the ".clone()" methods of any objects contained in
 * an instance of the class.
 * Hence, classes that implement JMLValueType have objects that are
 * "containers of values", in the sense that the user is interested
 * in the values referenced, not not simply the "addresses".
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLType
 */
//-@ immutable
//@ pure
public interface JMLValueType extends JMLType {

    /** Return a deep copy of this object.
     */
    /*@ also 
      @   public normal_behavior
      @     ensures \result instanceof JMLValueType
      @      && (* all externally-visible mutable objects
      @            contained directly in "this" must be cloned in \result. *);
      @ implies_that
      @  ensures (* no direct aliases are created between this and \result *);
      @*/
    public /*@ pure @*/ Object clone();    


    /** Compare with ob2 using .equals on underlying objects.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result ==>
      @        ob2 != null
      @        && (* all externally-visible objects contained in ob2 test
      @              as ".equals()" to the corresponding object in this
      @              (and vice versa) *);
      @*/
    public /*@ pure @*/ boolean equals(Object ob2);    
}
