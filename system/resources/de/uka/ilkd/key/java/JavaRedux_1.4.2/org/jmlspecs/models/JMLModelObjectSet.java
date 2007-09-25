// @(#)$Id: JMLModelObjectSet.java 1.2 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

/** A collection of object sets for use in set comprehensions.  All of
 * the public methods are model methods, because there is no way to
 * compute the set of all potential object identities of any given
 * type.
 *
 * <p> This type is not that useful, as you can mostly just use
 * quantification over the relevant type instead of one of these sets.
 * Indeed the sets are defined by using universal quantifiers, and so their
 * use is roughly equivalent.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens
 */
//-@ immutable
public /*@ pure @*/ class JMLModelObjectSet {

    /** The set of all (actual and potential) JMLByte objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLByte x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLBytes();
    @*/

    /** The set of all (actual and potential) JMLChar objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLChar x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLChars();
    @*/

    /** The set of all (actual and potential) JMLInteger objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLInteger x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLIntegers();
    @*/

    /** The set of all (actual and potential) JMLLong objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLLong x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLLongs();
    @*/

    /** The set of all (actual and potential) JMLShort objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLShort x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLShorts();
    @*/

    /** The set of all (actual and potential) JMLString objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLString x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLStrings();
    @*/

    /** The set of all (actual and potential) JMLFloat objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLFloat x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLFloats();
    @*/

    /** The set of all (actual and potential) JMLDouble objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLDouble x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLDoubles();
    @*/

    /** The set of all (actual and potential) Boolean objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
     @     ensures (\forall Boolean x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Booleans();
    @*/

    /** The set of all (actual and potential) Byte objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Byte x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Bytes();
    @*/

    /** The set of all (actual and potential) Character objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Character x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Characters();
    @*/

    /** The set of all (actual and potential) Integer objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Integer x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Integers();
    @*/

    /** The set of all (actual and potential) Long objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Long x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Longs();
    @*/

    /** The set of all (actual and potential) Short objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Short x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Shorts();
    @*/

    /** The set of all (actual and potential) String objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall String x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Strings();
    @*/

    /** The set of all (actual and potential) Float objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Float x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Floats();
    @*/

    /** The set of all (actual and potential) Double objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Double x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Doubles();
    @*/

    /** This class has no instances.
     */
    private JMLModelObjectSet() {}
}

