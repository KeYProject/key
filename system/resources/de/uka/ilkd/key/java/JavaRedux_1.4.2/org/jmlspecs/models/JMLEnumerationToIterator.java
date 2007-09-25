// @(#)$Id: JMLEnumerationToIterator.java 1.1.1.1 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

/** A wrapper that makes any {@link JMLEnumeration} into a {@link
 * JMLIterator} that does not support the remove operation.
 *
 * @version $Revision: 1.1.1.1 $
 * @author Gary T. Leavens
 * @see JMLEnumeration
 * @see JMLIterator
 * @see java.util.Iterator
 */
//-@ immutable
public class JMLEnumerationToIterator implements JMLIterator {

    protected final /*@ spec_public non_null @*/ JMLEnumeration theEnumeration;
    //@            maps theEnumeration.objectState \into objectState;

    /*@ public represents moreElements <- theEnumeration.hasMoreElements();
      @ public represents_redundantly
      @                   moreElements <- theEnumeration.moreElements;
      @*/

    /** Initialize this iterator with the given Enumeration.  The
     * enumeration is cloned.
     */
    /*@ public normal_behavior
      @   requires e != null;
      @   assignable owner, theEnumeration, elementType, moreElements;
      @   assignable returnsNull;
      @   ensures theEnumeration.equals(e);
      @   ensures owner == null;
      @*/
    public JMLEnumerationToIterator(/*@ non_null @*/ JMLEnumeration e) {
        Object o = e.clone();
        theEnumeration = (JMLEnumeration) o;
    }

    /** Tells whether this has more uniterated elements.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result == theEnumeration.moreElements;
      @     ensures_redundantly \result == theEnumeration.moreElements;
      @*/
    public /*@ pure @*/ boolean hasNext() {
        return theEnumeration.hasMoreElements();
    } 

    /** Return the next element in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     */
    /*@ also
      @   public normal_behavior
      @     requires moreElements;
      @     requires_redundantly hasNext();
      @     assignable objectState, moreElements, remove_called_since;
      @ also
      @   public exceptional_behavior
      @     requires !moreElements;
      @     requires_redundantly !hasNext();
      @     assignable \nothing;
      @     signals (JMLNoSuchElementException);
      @*/
    public Object next() throws JMLNoSuchElementException {
        Object result = theEnumeration.nextElement();
        return result;
    }

    /** The remove operation is not supported in this type.
     * So remove always throws an UnsupportedOperationException.
     */
    /*@ also
      @    signals (UnsupportedOperationException);
      @*/
    public void remove() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    /** Return a clone of this iterator.
     */
    public /*@ pure @*/ Object clone() {
        Object o = theEnumeration.clone();
        return new JMLEnumerationToIterator((JMLEnumeration) o);
    }

    /** Return true just when this iterator has the same state as
     * the given argument.
     */
    /*@ also
      @    public normal_behavior
      @      ensures \result <==> oth != null
      @           && oth instanceof JMLEnumerationToIterator
      @           && theEnumeration.equals(((JMLEnumerationToIterator) oth)
      @                                  .theEnumeration);
      @*/
    public /*@ pure @*/ boolean equals(Object oth) {
        return oth != null
            && oth instanceof JMLEnumerationToIterator
            && theEnumeration.equals(((JMLEnumerationToIterator) oth)
                                     .theEnumeration);
    }

    /** Return a hash code for this iterator.
     */
    public /*@ pure @*/ int hashCode() {
        return theEnumeration.hashCode();
    }
}
