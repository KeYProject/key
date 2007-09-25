// @(#)$Id: JMLSetEnumerator.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

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

import java.util.Enumeration;

/** An enumerator for sets of _ElemType_English_s.
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLEnumeration
 * @see _SuperType_
 * @see JML_Elem_Set
 * @see JMLEnumerationToIterator
 */
//-@ immutable
public class JML_Elem_SetEnumerator
    implements JMLEnumeration, _SuperType_
{

    /** The elements that have not yet been returned by nextElement.
     */
    //@ public model JML_Elem_Set uniteratedElems;        in objectState;
    //@ public invariant uniteratedElems != null;

    /** The list representing the elements that have not yet been
     * returned by this enumerator.
     */
    protected JMLList_Elem_Node currentNode;
    //@                               in uniteratedElems;

    //@ protected represents uniteratedElems <- new JML_Elem_Set(currentNode);

    //@ protected invariant moreElements <==> currentNode != null;

    //@ public invariant elementType <: \type(_ElemType_);

    /*@ public invariant
      @       !uniteratedElems.isEmpty()
      @        ==> uniteratedElems.elementType <: elementType;
      @*/

    //@ public constraint returnsNull == \old(returnsNull);

    /*@ public invariant
      @       !returnsNull
      @         ==> uniteratedElems.isEmpty() || !uniteratedElems.containsNull;
      @*/

    /** Initialize this with the given set.
     */
    /*@ normal_behavior
      @   requires s != null;
      @   assignable uniteratedElems;
      @   modifies moreElements, elementType, returnsNull, owner;
      @   ensures uniteratedElems.equals(s);
      @   ensures owner == null;
      @   ensures elementType == s.elementType;
      @   ensures returnsNull == s.containsNull;
      @*/
    JML_Elem_SetEnumerator(/*@ non_null @*/ JML_Elem_Set s) {
        //@ set owner = null;
        //@ set elementType = s.elementType;
        //@ set returnsNull = s.containsNull;
        currentNode = s.the_list;
    }

    /** Tells whether this enumerator has more uniterated elements.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result == !uniteratedElems.isEmpty();
      @*/
    public /*@ pure @*/ boolean hasMoreElements() {
        return currentNode != null;
    }

    /** Return the next element in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     */
    /*@ also
      @   public normal_behavior
      @     requires hasMoreElements();
      @     assignable uniteratedElems, moreElements;
      @     ensures
      @        (\result == null
      @           ==> \old(uniteratedElems).has(null)
      @               && uniteratedElems.equals(\old(uniteratedElems)
      @                                      .remove(null)))
      @       && (\result != null
      @           ==> \old(uniteratedElems).has(_elem_downcast_\result)
      @               && uniteratedElems.equals(\old(uniteratedElems)
      @                                      .remove(_elem_downcast_\result)));
      @ also
      @   public exceptional_behavior
      @     requires !hasMoreElements();
      @     assignable \nothing;
      @     signals (JMLNoSuchElementException);
      @*/
    public Object nextElement() throws JMLNoSuchElementException {
        if (currentNode != null) {
            _ElemType_ retValue = currentNode.val;
            //@ assume retValue != null ==> \typeof(retValue) <: elementType;
            //@ assume retValue == null ==> returnsNull;
            currentNode = currentNode.next;
            return retValue;
        } else {
            throw new JMLNoSuchElementException("Tried to .nextElement() "
                                                + "with JML_Elem_Set "
                                                + "Enumerator `off the end'");
        }
    }

    /** Return a clone of this enumerator.
     */
    public Object clone() {
        return new JML_Elem_SetEnumerator(new JML_Elem_Set(currentNode));
    } //@ nowarn Post;

    /** Return true just when this enumerator has the same state as
     * the given argument.
     */
    public /*@ pure @*/ boolean equals(Object oth) {
        if  (oth == null || !(oth instanceof JML_Elem_SetEnumerator)) {
            return false;
        } else {
            JML_Elem_SetEnumerator js = (JML_Elem_SetEnumerator) oth;
            if (currentNode == null) {
                return js.currentNode == null;
            } else {
                return currentNode.equals(js.currentNode);
            }
        }
    }

    /** Return a hash code for this enumerator.
     */
    public int hashCode() {
        return currentNode == null ? 0 : currentNode.hashCode();
    }
}
