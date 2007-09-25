// @(#)$Id: JMLEqualsBagEnumerator.java 1.2 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

/** Enumerators for bags (i.e., multisets) of objects.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLEnumeration
 * @see JMLType
 * @see JMLEqualsBag
 * @see JMLEnumerationToIterator
 */
//-@ immutable
public class JMLEqualsBagEnumerator
    implements JMLEnumeration, JMLObjectType
{
    /** The elements that have not yet been returned by nextElement.
     */
    //@ public model JMLEqualsBag uniteratedElems;   in objectState;

    /** The bag underlying this enumerator.
     */
    protected /*@ non_null @*/ JMLEqualsBag currentBag;
    //@                                        in uniteratedElems;

    /** The remaining count of repetitions that the current entry
     * should be returned.
     */
    protected int currentCount;
    //@                 in uniteratedElems;

    /** The current entry.
     */
    protected Object currEntry;
    //@                     in uniteratedElems;

    /*@ protected represents
      @     uniteratedElems <- currentBag.removeAll(currEntry)
      @                                  .insert(currEntry, currentCount);
      @*/

    //@ protected invariant currentCount >= 0;

    /*@ protected invariant currentCount > 0
      @            ==> (* currEntry is holds an element, which may be null *);
      @ protected invariant !currentBag.isEmpty()
      @      ==> currentBag.has(currEntry)
      @          && currentCount <= currentBag.count(currEntry);
      @*/

    //@ protected invariant currentCount > 0 ==> moreElements;
    /*@ protected invariant moreElements <==>
      @               (currentCount > 0 || !currentBag.isEmpty());
      @*/

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

    /** Initialize this with the given bag.
     */
    /*@ normal_behavior
      @   requires b != null;
      @   assignable uniteratedElems;
      @   assignable moreElements, elementType, returnsNull, owner;
      @   ensures uniteratedElems.equals(b);
      @    ensures owner == null;
      @    ensures elementType == b.elementType;
      @    ensures returnsNull == b.containsNull;
      @*/
    JMLEqualsBagEnumerator(/*@ non_null @*/ JMLEqualsBag b) {
        currentBag = b;
        if (!currentBag.isEmpty()) {
            currEntry = currentBag.choose();
            currentCount = currentBag.count(currEntry);
        } else {
            currentCount = 0;
        }
    }

    /** Tells whether this enumerator has more uniterated elements.
     */
    /*@ also
      @   public normal_behavior
      @   ensures \result == !uniteratedElems.isEmpty();
      @   ensures_redundantly \result == moreElements;
      @   ensures_redundantly \result <==> !uniteratedElems.isEmpty();
      @   ensures_redundantly \result <=!=> uniteratedElems.isEmpty();
      @   ensures_redundantly \result != uniteratedElems.isEmpty();
      @*/
    public /*@ pure @*/ boolean hasMoreElements() {
        boolean ret = currentCount > 0 || !currentBag.isEmpty();
        return ret;
    }

    /** Return the next element in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     */
    /*@ also
      @   public normal_behavior
      @     requires hasMoreElements();
      @     assignable uniteratedElems, moreElements;
      @     ensures \old(uniteratedElems).has(\result)
      @       && uniteratedElems.equals(\old(uniteratedElems)
      @             .remove(\result));
      @ also
      @   public exceptional_behavior
      @     requires !hasMoreElements();
      @     assignable \nothing;
      @     signals (JMLNoSuchElementException);
      @*/
    public Object nextElement() throws JMLNoSuchElementException {
        if (currentCount > 0 || !currentBag.isEmpty()) {
            Object retValue;
            if (currEntry == null) {
                retValue = null;
            } else {
                retValue = (Object)currEntry;
            }
            currentCount--;
            if (currentCount <= 0) {
                // The following gratiutious assignment is added because
                // ESC/Java imagines that a callback may happen...
                currentCount = 0;
                currentBag = currentBag.removeAll(currEntry);
                if (currentBag.isEmpty()) {
                    currentCount = 0;
                } else {
                    currEntry = currentBag.choose();
                    currentCount = currentBag.count(currEntry);
                }
            }
            return retValue;
        } else {
            throw new JMLNoSuchElementException("Tried to .nextElement() "
                                                + "with JMLEqualsBag "
                                                + "Enumerator `off the end'");
        }
    }

    /** Return a clone of this enumerator.
     */
    public Object clone() {
        return new JMLEqualsBagEnumerator(abstractValue());
    } 

    /** Return the abstract value of this bag enumerator.
     */
    protected /*@ pure non_null @*/ JMLEqualsBag abstractValue() {
        JMLEqualsBag absVal = currentBag;
        if (currentCount > 0) {
            absVal = currentBag.removeAll(currEntry).insert(currEntry,
                                                            currentCount);
        }
        return absVal;
    } 

    /** Return true just when this enumerator has the same state as
     * the given argument..
     */
    public boolean equals(Object oth) {
        if  (oth == null || !(oth instanceof JMLEqualsBagEnumerator)) {
            return false;
        } else {
            JMLEqualsBagEnumerator jb = (JMLEqualsBagEnumerator) oth;
            return this.abstractValue().equals(jb.abstractValue());
        }
    }

    /** Return a hash code for this enumerator.
     */
    public int hashCode() {
        return abstractValue().hashCode();
    }
}
