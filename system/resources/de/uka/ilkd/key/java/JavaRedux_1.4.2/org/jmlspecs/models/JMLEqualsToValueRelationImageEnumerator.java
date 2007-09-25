// @(#)$Id: JMLEqualsToValueRelationImageEnumerator.java 1.2 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

/** Enumerator for pairs of keys and their relational images.  This
 *  enumerator returns pairs of type {@link JMLEqualsValuePair},
 *  each of which has a "key" field of type {@link Object} and a
 *  "value" field of type {@link JMLValueSet}s containing {@link
 *  JMLType}.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens
 * @see JMLEnumeration
 * @see JMLValueType
 * @see JMLEqualsToValueRelationEnumerator
 * @see JMLEqualsToValueRelation
 * @see JMLEqualsToValueMap
 * @see JMLEnumerationToIterator
 * @see JMLValueSet
 */
//-@ immutable
public class JMLEqualsToValueRelationImageEnumerator
    implements JMLEnumeration, JMLValueType {

    //@ public model JMLValueSet uniteratedImagePairs;     in objectState;

    /** An enumerator for the image pairs in this relation.
     */
    protected /*@ non_null @*/ JMLValueSetEnumerator pairEnum;
    //@                                             in uniteratedImagePairs;

    /*@ protected represents uniteratedImagePairs <- abstractValue();
      @*/

    /*@ protected
      @   invariant moreElements <==> pairEnum.moreElements;
      @*/

    //@ public invariant elementType == \type(JMLEqualsValuePair);
    //@ public invariant !returnsNull;

    /** Initialize this with the given relation.
     */
    /*@ normal_behavior
      @   requires rel != null;
      @   assignable uniteratedImagePairs;
      @   assignable moreElements, elementType, returnsNull, owner;
      @   ensures uniteratedImagePairs.equals(rel.imagePairSet());
      @    ensures owner == null;
      @*/
    JMLEqualsToValueRelationImageEnumerator(/*@ non_null @*/
                                           JMLEqualsToValueRelation rel)
    {
        pairEnum = rel.imagePairSet_.elements();
    }

    /*@ normal_behavior
      @   requires pEnum != null;
      @   assignable uniteratedImagePairs;
      @   assignable moreElements, elementType, returnsNull, owner;
      @   ensures owner == null;
      @*/
    protected
        JMLEqualsToValueRelationImageEnumerator(/*@ non_null @*/
                                                   JMLValueSetEnumerator pEnum)
    {
        pairEnum =  (JMLValueSetEnumerator)pEnum.clone();
    }

    /** Tells whether this enumerator has more uniterated elements.
     *  @see #nextElement
     *  @see #nextImagePair
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result == !uniteratedImagePairs.isEmpty();
      @*/
    public boolean hasMoreElements() {
        return pairEnum.hasMoreElements();
    }

    /** Return the next image pair in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     *  @see #hasMoreElements
     *  @see #nextImagePair
     */
    /*@ also
      @  public normal_behavior
      @    requires !uniteratedImagePairs.isEmpty();
      @    assignable uniteratedImagePairs;
      @    ensures \old(uniteratedImagePairs).has((JMLType)\result)
      @        && uniteratedImagePairs
      @           .equals(\old(uniteratedImagePairs).remove((JMLType)\result));
      @ also
      @  public exceptional_behavior
      @    requires uniteratedImagePairs.isEmpty();
      @    assignable \nothing;
      @    signals (JMLNoSuchElementException);
      @*/
    public Object nextElement() throws JMLNoSuchElementException {
        if (pairEnum.hasMoreElements()) {
            Object o = pairEnum.nextElement();
            return o;
        } else {
            throw new JMLNoSuchElementException();
        }
    }

    /** Return the next image pair in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     *  @see #hasMoreElements
     *  @see #nextElement
     */
    /*@ public normal_behavior
      @    requires !uniteratedImagePairs.isEmpty();
      @    assignable uniteratedImagePairs, moreElements;
      @    ensures \old(uniteratedImagePairs).has(\result)
      @         && uniteratedImagePairs.equals(
      @               \old(uniteratedImagePairs).remove(\result));
      @ also
      @  public exceptional_behavior
      @    requires uniteratedImagePairs.isEmpty();
      @    assignable \nothing;
      @    signals (JMLNoSuchElementException);
      @
      @ also
      @    modifies uniteratedImagePairs;
      @    modifies moreElements;
      @    ensures \old(moreElements);
      @    signals (JMLNoSuchElementException) \old(!moreElements);
      @*/
    public /*@ non_null @*/ JMLEqualsValuePair nextImagePair()
        throws JMLNoSuchElementException {
        Object p = nextElement();
        JMLEqualsValuePair aPair = (JMLEqualsValuePair) p;
        return aPair;
    } 

    /** Return a clone of this enumerator.
     */
    public Object clone() {
        return new JMLEqualsToValueRelationImageEnumerator(pairEnum);
    } 

    /** Return true just when this enumerator has the same state as
     *  the given argument.
     */
    public boolean equals(Object oth) {
        if  (oth == null
             || !(oth instanceof JMLEqualsToValueRelationImageEnumerator)){
            return false;
        } else {
            JMLEqualsToValueRelationImageEnumerator js
                = (JMLEqualsToValueRelationImageEnumerator) oth;
            return abstractValue().equals(js.abstractValue());
        }
    }

    /** Return a hash code for this enumerator.
     */
    public int hashCode() {
        return abstractValue().hashCode();
    }

    /** Return the set of uniterated pairs from this enumerator.
     */
    protected /*@ spec_public pure @*/ /*@ non_null @*/
        JMLValueSet abstractValue()
    {
        JMLValueSet ret = new JMLValueSet();
        JMLEqualsToValueRelationImageEnumerator enum2
            = (JMLEqualsToValueRelationImageEnumerator) clone();
        while (enum2.hasMoreElements()) {
            JMLEqualsValuePair aPair = enum2.nextImagePair();
            ret = ret.insert(aPair);
        }
        return ret;
    } 
}
