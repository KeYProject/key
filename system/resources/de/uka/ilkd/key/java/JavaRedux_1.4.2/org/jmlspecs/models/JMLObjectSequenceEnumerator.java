// @(#)$Id: JMLObjectSequenceEnumerator.java 1.2 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

import java.util.Enumeration;

/** An enumerator for sequences of objects.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLEnumeration
 * @see JMLType
 * @see JMLObjectSequence
 * @see JMLValueSequence
 * @see JMLEnumerationToIterator
 */
//-@ immutable
public class JMLObjectSequenceEnumerator
    implements JMLEnumeration, JMLObjectType
{

    /** The elements that have not yet been returned by nextElement.
     */
    //@ public model JMLObjectSequence uniteratedElems; in objectState;
    //@ public invariant uniteratedElems != null;

    /** The list representing the elements yet to be returned.
     */
    protected JMLListObjectNode currentNode;
    //@                               in uniteratedElems;

    /** The number of elements remaining to return.
     */
    protected /*@ spec_public @*/ int remaining;
    //@                                  in uniteratedElems;

    /*@ protected represents uniteratedElems
      @                  <- new JMLObjectSequence(currentNode, remaining);
      @*/

    //@ public invariant moreElements <==> remaining != 0;
    //@ public invariant remaining >= 0;
    //@ protected invariant currentNode == null <==> remaining == 0;

    //@ public invariant elementType <: \type(Object);

    /*@ public invariant
      @       !uniteratedElems.isEmpty()
      @        ==> uniteratedElems.elementType <: elementType;
      @*/

    //@ public constraint returnsNull == \old(returnsNull);

    /*@ public invariant
      @       !returnsNull
      @         ==> uniteratedElems.isEmpty() || !uniteratedElems.containsNull;
      @*/

    /** Initialize this with the given sequence.
     */
    /*@ normal_behavior
      @   requires s != null;
      @   assignable uniteratedElems;
      @   assignable  moreElements, elementType, returnsNull, owner;
      @   ensures uniteratedElems.equals(s);
      @   ensures owner == null;
      @   ensures elementType == s.elementType;
      @   ensures returnsNull == s.containsNull;
      @*/
    JMLObjectSequenceEnumerator(/*@ non_null @*/ JMLObjectSequence s) {
        remaining = s.int_length();
        currentNode = s.theSeq;
    }

    /** Tells whether this enumerator has more uniterated elements.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result == !uniteratedElems.isEmpty();
      @    ensures \result <==> remaining > 0;
      @*/
    public /*@ pure @*/ boolean hasMoreElements() {
        return currentNode != null;
    }

    /** Return the next element in the sequence, counting up, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     */
    /*@ also
      @  public normal_behavior
      @    requires hasMoreElements();
      @    assignable uniteratedElems, moreElements;
      @    ensures \old(uniteratedElems).itemAt(0) == \result
      @         && uniteratedElems.equals(\old(uniteratedElems).trailer());
      @ also
      @  public exceptional_behavior
      @    requires !hasMoreElements();
      @    assignable \nothing;
      @    signals (JMLNoSuchElementException);
      @ also
      @  protected normal_behavior 
      @    requires remaining > 0;
      @    assignable uniteratedElems, moreElements;
      @    assignable_redundantly currentNode, remaining;
      @    ensures currentNode == \old(currentNode.next)
      @         && remaining == \old(remaining - 1);
      @*/
    public Object nextElement() throws JMLNoSuchElementException {
        if (currentNode != null) {
            Object retValue = currentNode.val;
            currentNode = currentNode.next;
            remaining = remaining - 1;
            return retValue;
        } else {
            throw new JMLNoSuchElementException("Tried to .nextElement() "
                                                + "with JMLObjectSequence "
                                                + "Enumerator `off the end'");
        }
    }

    /** Return a clone of this enumerator.
     */
    public Object clone() {
        return
            new JMLObjectSequenceEnumerator(new JMLObjectSequence(currentNode,
                                                                  remaining));
    } 

    /** Return true just when this enumerator has the same state as
     * the given argument..
     */
    public boolean equals(Object oth) {
        if  (oth == null || !(oth instanceof JMLObjectSequenceEnumerator)) {
            return false;
        } else {
            JMLObjectSequenceEnumerator js
                = (JMLObjectSequenceEnumerator) oth;
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
