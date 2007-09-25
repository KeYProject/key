// @(#)$Id: JMLModelValueSet.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

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

/** A collection of value sets for use in set comprehensions.  The
 * normal (non-model) methods might potentially be useful in executing
 * assertions, although the sets of all integers and longs can't
 * realistically be used in a direct way.  The model methods have no
 * hope of being executed.
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 * @see JMLValueSet
 */
//-@ immutable
public /*@ pure @*/ class JMLModelValueSet {

    /** This class has no instances.
     */
    private JMLModelValueSet() {}

    /** The set of all (actual and potential) JMLByte values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall byte i;
      @               (\exists JMLByte j; \result.has(j) && j != null;
      @                                   j.theByte == i ));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ JMLValueSet JMLBytes() {
        JMLValueSet ret = null;
        if (ret == null) {
            ret = new JMLValueSet(new JMLByte(Byte.MAX_VALUE));
            for (byte i = Byte.MIN_VALUE; i < Byte.MAX_VALUE; i++) {
                ret = ret.insert(new JMLByte(i));
            }
        }
        return ret;
    } //@ nowarn Exception;

    /** The set of all (actual and potential) JMLChar values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall char i;
      @               (\exists JMLChar j; \result.has(j) && j != null;
      @                                   j.theChar == i ));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ JMLValueSet JMLChars() {
        JMLValueSet ret = null;
        if (ret == null) {
            ret = new JMLValueSet(new JMLChar(Character.MAX_VALUE));
            for (char i = Character.MIN_VALUE; i < Character.MAX_VALUE; i++) {
                ret = ret.insert(new JMLChar(i));
            }
        }
        return ret;
    } //@ nowarn Exception;

    /** The set of all (actual and potential) JMLShort values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall short i;
      @               (\exists JMLShort j; \result.has(j) && j != null;
      @                                   j.theShort == i ));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ JMLValueSet JMLShorts() {
        JMLValueSet ret = null;
        if (ret == null) {
            ret = new JMLValueSet(new JMLShort(Short.MAX_VALUE));
            for (short i = Short.MIN_VALUE; i < Short.MAX_VALUE; i++) {
                ret = ret.insert(new JMLShort(i));
            }
        }
        return ret;
    } //@ nowarn Exception;

    /** The set of all (actual and potential) JMLInteger values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall int i; 
      @               (\exists JMLInteger j; \result.has(j) && j != null;
      @                                   j.theInt == i ));
    public static pure model non_null JMLValueSet JMLIntegers();
    @*/


    // ********* The following aren't ever going to be executable. *******


    /** The set of all (actual and potential) JMLLong values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall long i; 
      @               (\exists JMLLong j; \result.has(j) && j != null;
      @                                   j.theLong == i ));
    public static pure model non_null JMLValueSet JMLLongs();
    @*/


    /** The set of all (actual and potential) JMLString values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall String s; s != null;
      @               (\exists JMLString js; \result.has(js) && js != null;
      @                                      js.theString.equals(s) ));
    public static pure model non_null JMLValueSet JMLStrings();
    @*/

    /** The set of all (actual and potential) JMLFloat values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall float f;
      @               (\exists JMLFloat jf; \result.has(jf) && jf != null;
      @                                   (Float.isNaN(f) && jf.isNaN())
      @                                    || jf.theFloat == f ));
    public static pure model non_null JMLValueSet JMLFloats();
    @*/

    /** The set of all (actual and potential) JMLDouble values.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall double f;
      @               (\exists JMLDouble jf; \result.has(jf) && jf != null;
      @                                   (Double.isNaN(f) && jf.isNaN())
      @                                    || jf.theDouble == f ));
    public static pure model non_null JMLValueSet JMLDoubles();
    @*/
}

