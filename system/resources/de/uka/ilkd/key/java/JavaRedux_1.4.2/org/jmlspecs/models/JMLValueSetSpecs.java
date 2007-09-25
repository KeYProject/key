// @(#)$Id: JMLValueSetSpecs.java 1.3 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

/** Special behavior for JMLValueSet not shared by JMLObjectSet.
 *
 * @version $Revision: 1.3 $
 * @author Gary T. Leavens, with help from Clyde Ruby, and others.
 * @see JMLValueType
 * @see JMLValueSet
 */
//-@ immutable
public /*@ pure @*/ abstract class JMLValueSetSpecs implements JMLValueType {

    /** Is the argument ".equals" to one of the values in the set.
     *  @see #has(Object)
     */
    public abstract boolean has(JMLType elem);

    /** Is the argument ".equals" to one of the values in theSet.
     *  @see #has(JMLType)
     */
    /*@   public normal_behavior
      @     requires elem != null;
      @     ensures \result
      @        <==> elem instanceof JMLType && has((JMLType)elem);
      @ also
      @   public normal_behavior
      @     requires elem == null;
      @     ensures \result == has(null);
      @*/    
    public boolean has(Object elem ) {
        if (elem == null) {
            return has(null);
        } else {
            return elem instanceof JMLType && has((JMLType)elem);
        }
    }  

    /** Tells the number of elements in the set.
     */
    /*@ public normal_behavior
      @   ensures \result >= 0
      @        && (* \result is the number of elements in the set *);
      @*/
    public abstract int int_size(); 

    // Specification inherited from JMLValueType.
    // Note: not requiring the \result contain "clones" of the elements of 
    // this, allows the implementer latitude to take advantage of the
    // nature of immutable types.
    public abstract Object clone();

    /** Is the argument one of the objects representing values in the set?
     *  @see #has(Object)
     */
    /*@ public normal_behavior
        ensures true;  
	public model boolean hasObject(JMLType elem); 
      @*/
    /** Returns a new set that contains all the elements of this and
     *  also the given argument.
     */
    public abstract /*@ non_null @*/ JMLValueSet insert (JMLType elem);

}
