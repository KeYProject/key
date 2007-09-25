// @(#)$Id: JMLObjectToObjectRelationEnumerator.java 1.2 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

/** Enumerator for pairs of keys of type {@link Object} to
 * values of type {@link Object} that form the associations in a
 * relation.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens
 * @see JMLEnumeration
 * @see JMLValueType
 * @see JMLObjectToObjectRelationImageEnumerator
 * @see JMLObjectToObjectRelation
 * @see JMLObjectToObjectMap
 * @see JMLEnumerationToIterator
 * @see JMLValueSet
 */
//-@ immutable
public class JMLObjectToObjectRelationEnumerator
    implements JMLEnumeration, JMLValueType {

    //@ public model JMLValueSet uniteratedPairs;      in objectState;

    /** An enumerator for the image pairs in this relation.
     */
    protected /*@ non_null @*/
        JMLObjectToObjectRelationImageEnumerator imagePairEnum;
    //@                                                in uniteratedPairs;

    /** The current key for pairs being enumerated.
     */
    protected Object key;
    //@                     in uniteratedPairs;

    /** An enumerator for the range elements that are related to the
     *  key that have not yet been returned.
     */
    protected /*@ non_null @*/ JMLObjectSetEnumerator imageEnum;
    //@                                                   in uniteratedPairs;


    /*@ protected represents uniteratedPairs <- abstractValue();
      @*/

    /*@ protected invariant moreElements
      @             <==> imageEnum.moreElements|| imagePairEnum.moreElements;
      @*/

    /*@ protected invariant moreElements ==> key != null;
      @*/

    //@ public invariant elementType == \type(JMLObjectObjectPair);
    //@ public invariant !returnsNull;

    /** Initialize this with the given relation.
     */
    /*@ normal_behavior
      @   requires rel != null;
      @   assignable uniteratedPairs;
      @   assignable moreElements, elementType, returnsNull, owner;
      @   ensures uniteratedPairs.equals(rel.theRelation);
      @    ensures owner == null;
      @*/
    JMLObjectToObjectRelationEnumerator(/*@ non_null @*/
                                           JMLObjectToObjectRelation rel) {
        imagePairEnum = rel.imagePairs();
        if (imagePairEnum.hasMoreElements()) {
            JMLObjectValuePair p = imagePairEnum.nextImagePair();
            key = p.key;
            imageEnum = ((JMLObjectSet)p.value).elements();
        } else {
            key = null;
            imageEnum = (new JMLObjectSet()).elements();
        }
    }

    /*@ requires ipEnum != null;
      @ requires iEnum != null;
      @ requires (ipEnum.moreElements || iEnum.moreElements) ==> k != null;
      @*/
    protected
        JMLObjectToObjectRelationEnumerator(JMLObjectToObjectRelationImageEnumerator ipEnum,
                                               JMLObjectSetEnumerator iEnum,
                                               Object k) {
        imagePairEnum
            = (JMLObjectToObjectRelationImageEnumerator)ipEnum.clone();
        imageEnum = (JMLObjectSetEnumerator)iEnum.clone();
        key = k;
    }

    /** Tells whether this enumerator has more uniterated elements.
     *  @see #nextElement
     *  @see #nextPair
     */
    /*@ also
      @  public normal_behavior
      @    assignable \nothing;
      @    ensures \result == !uniteratedPairs.isEmpty();
      @*/
    public /*@ pure @*/ boolean hasMoreElements() {
        return (imagePairEnum.hasMoreElements() || imageEnum.hasMoreElements());
    }

    /** Return the next image pair in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     *  @see #hasMoreElements
     *  @see #nextPair
     */
    /*@ also
      @  public normal_behavior
      @    requires !uniteratedPairs.isEmpty();
      @    assignable uniteratedPairs;
      @    ensures \old(uniteratedPairs).has((JMLType)\result)
      @         && uniteratedPairs.
      @                equals(\old(uniteratedPairs).remove((JMLType)\result));
      @ also
      @  public exceptional_behavior
      @    requires uniteratedPairs.isEmpty();
      @    assignable \nothing;
      @    signals (JMLNoSuchElementException);
      @*/
    public Object nextElement() throws JMLNoSuchElementException {
        if (imageEnum.hasMoreElements()) {
            Object v = imageEnum.nextElement();
            return new JMLObjectObjectPair(key, (Object)v);
        } else if (imagePairEnum.hasMoreElements()) {
            Object p = imagePairEnum.nextElement();
            JMLObjectValuePair imagePair = (JMLObjectValuePair) p;
            key = imagePair.key;
            imageEnum = ((JMLObjectSet)imagePair.value).elements();
            Object v = imageEnum.nextElement();
            return new JMLObjectObjectPair(key, (Object)v);
        } else {
            throw new JMLNoSuchElementException();
        }
    }

    /** Return the next pair in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     *  @see #hasMoreElements
     *  @see #nextElement
     */
    /*@ public normal_behavior
      @    requires !uniteratedPairs.isEmpty();
      @    assignable uniteratedPairs, moreElements;
      @    ensures \old(uniteratedPairs).has(\result)
      @         && uniteratedPairs
      @            .equals(\old(uniteratedPairs).remove(\result));
      @ also
      @  public exceptional_behavior
      @    requires uniteratedPairs.isEmpty();
      @    assignable \nothing;
      @    signals (JMLNoSuchElementException);
      @
      @ also
      @   modifies uniteratedPairs;
      @   modifies moreElements;
      @   ensures \old(moreElements);
      @   signals (JMLNoSuchElementException) \old(!moreElements);
      @*/
    public /*@ non_null @*/ JMLObjectObjectPair nextPair()
        throws JMLNoSuchElementException {
        Object p = nextElement();  
        JMLObjectObjectPair aPair = (JMLObjectObjectPair) p;
        return aPair;
    } 

    /** Return a clone of this enumerator.
     */
    public Object clone() {
        return new JMLObjectToObjectRelationEnumerator(imagePairEnum,
                                                          imageEnum,
                                                          key);
    } 

    /** Return true just when this enumerator has the same state as
     *  the given argument.
     */
    public /*@ pure @*/ boolean equals(Object oth) {
        if  (oth == null
             || !(oth instanceof JMLObjectToObjectRelationEnumerator)) {
            return false;
        } else {
            JMLObjectToObjectRelationEnumerator js
                = (JMLObjectToObjectRelationEnumerator) oth;
            return abstractValue().equals(js.abstractValue());
        }
    }

    /** Return a hash code for this enumerator.
     */
    public /*@ pure @*/ int hashCode() {
        return abstractValue().hashCode();
    }

    /** Return the set of uniterated pairs from this enumerator.
     */
    protected /*@ spec_public pure @*/ /*@ non_null @*/
        JMLValueSet abstractValue()
    {
        JMLValueSet ret = new JMLValueSet();
        JMLObjectToObjectRelationEnumerator enum2
            = (JMLObjectToObjectRelationEnumerator) clone();
        while (enum2.hasMoreElements()) {
            JMLObjectObjectPair aPair = enum2.nextPair();
            ret = ret.insert(aPair);
        }
        return ret;
    } 
}
