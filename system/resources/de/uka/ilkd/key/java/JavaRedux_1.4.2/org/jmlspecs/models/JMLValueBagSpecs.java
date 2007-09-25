// @(#)$Id: JMLValueBagSpecs.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

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

/** Special behavior for JMLValueBag not shared by JMLObjectBag.
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens, with help from Clyde Ruby, and others.
 * @see JMLValueType
 * @see JMLValueBag
 */
//-@ immutable
public /*@ pure @*/ abstract class JMLValueBagSpecs implements JMLValueType {

    /** Is the argument ".equals" to one of the values in this bag.
     *  @see #has(Object)
     *  @see #count(JMLType)
     */
    /*@ public normal_behavior
      @   ensures \result <==> count(elem) > 0;
      @*/
    public abstract boolean has(JMLType elem);

    /** Is the argument ".equals" to one of the values in this bag.
     *  @see #has(JMLType)
     *  @see #count(Object)
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
    public boolean has(Object elem) {
        if (elem == null) {
            return has(null);
        } else {
            return elem instanceof JMLType && has((JMLType)elem);
        }
    }  

    /** Tell many times the argument occurs ".equals" to one of the
     * values in this bag.
     *  @see #count(Object)
     *  @see #has(JMLType)
     */
    /*@ public normal_behavior
      @   ensures \result >= 0;
      @*/
    public abstract int count(JMLType elem);

    /** Tell many times the argument occurs ".equals" to one of the
     * values in this bag.
     *  @see #count(JMLType)
     *  @see #has(Object)
     */
    /*@   public normal_behavior
      @     requires elem != null;
      @     ensures \result
      @          == (elem instanceof JMLType ? count((JMLType)elem) : 0);
      @ also
      @   public normal_behavior
      @     requires elem == null;
      @     ensures \result == count(null);
      @*/    
    public int count(Object elem) {
        if (elem == null) {
            return count(null);
        } else {
            return (elem instanceof JMLType ? count((JMLType)elem) : 0);
        }
    }  

    /** Tells the number of elements in the bag.
     */
    /*@ public normal_behavior
      @   ensures \result >= 0;
      @*/
    public abstract int int_size();

    // Specification inherited from JMLValueType.
    // Note: not requiring the \result contain "clones" of the elements of 
    // this, allows the implementer latitude to take advantage of the
    // nature of immutable types.
    public abstract Object clone();


    /*@ public normal_behavior
      @   requires true;
      @ public model int countObject(JMLType elem); 
      @*/

    public abstract /*@ non_null @*/ JMLValueBag insert (JMLType elem)
        ;

    /*@
      @    signals (IllegalArgumentException) cnt < 0;
      @*/
    public abstract /*@ non_null @*/ JMLValueBag insert (JMLType elem,
                                                         int cnt)
        throws IllegalArgumentException;

}
