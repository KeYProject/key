// @(#)$Id: JMLObjectSequence.java 1.3 Mon, 09 May 2005 15:27:50 +0200 engelc $

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
import java.math.BigInteger;

/** Sequences of objects.  This type uses "=="
 * to compare elements, and does not clone elements that are passed into
 * and returned from the sequence's methods.
 *
 * <p> The informal model for a JMLObjectSequence is a finite
 * mathematical sequence of elements (of type {@link Object}). In
 * some examples, we will write
 * &lt;<em>a</em>,<em>b</em>,<em>c</em>&gt; for a mathematical
 * sequence of length 3, containing elements <em>a</em>, <em>b</em>,
 * and <em>c</em>. Elements of sequences are "indexed" from 0, so the
 * length of a sequence is always 1 more than the index of the last
 * element in the sequence.
 *
 * @version $Revision: 1.3 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLCollection
 * @see JMLType
 * @see JMLValueSequence
 * @see JMLObjectSequenceEnumerator
 * 
 */
//-@ immutable
public /*@ pure @*/ class JMLObjectSequence
    implements JMLCollection
{

    //*********************** equational theory ***********************

    /*@ public invariant (\forall JMLObjectSequence s2;
      @                    (\forall Object e1, e2;
      @                     (\forall \bigint n;
      @                       equational_theory(this, s2, e1, e2, n) )));
      @*/

    /** An equational specification of the properties of sequences.
     */
    /*@ public normal_behavior
      @ {|
      @  // The following are defined by observations (itemAt) and induction.
      @ 
      @    ensures \result <==> !(new JMLObjectSequence()).has(e1);
      @  also
      @    ensures \result <==> (new JMLObjectSequence()).size() == 0;
      @  also
      @    ensures \result <==> (new JMLObjectSequence(e1)).size() == 1;
      @  also
      @    ensures \result <==> 
      @        e1 != null ==>
      @        (new JMLObjectSequence(e1)).itemAt(0) == e1;
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).first() == e1;
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).last() == e1;
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).itemAt(0) == e1;
      @  also
      @    ensures \result <==>
      @        s.insertFront(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).itemAt(s.size()) == e1;
      @  also
      @    ensures \result <==>
      @        s.insertBack(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==> 
      @    // !FIXME! The following may be inconsistent: argument to itemAt might
      @    // be equal to size, but it is required to be less than size.
      @        -1 <= n && n < s.size() && e1 != null
      @          ==> s.insertAfterIndex(n, e1).itemAt(n+1) == e1;
      @  also
      @    ensures \result <==> 
      @        -1 <= n && n < s.size()
      @          ==> s.insertAfterIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        0 <= n && n <= s.size() && e1 != null
      @          ==> s.insertBeforeIndex(n, e1).itemAt(n) == e1;
      @  also
      @    ensures \result <==> 
      @        0 <= n && n <= s.size()
      @          ==> s.insertBeforeIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        s.isPrefix(s2)
      @           == (\forall int i; 0 <= i && i < s.int_length();
      @                  (s2.itemAt(i) != null 
      @                   && s2.itemAt(i) == (s.itemAt(i)))
      @               || (s2.itemAt(i) == null && s.itemAt(i) == null) );
      @  also
      @    ensures \result <==>
      @        s.isSubsequence(s2)
      @           == s.int_length() <= s2.int_length()
      @              && (s.isPrefix(s2) || s.isSubsequence(s2.trailer()) );
      @ 
      @   // The following are all defined as abbreviations.
      @
      @ also
      @   ensures \result <==>
      @      s.isEmpty() == (s.size() == 0);
      @ also
      @   ensures \result <==>
      @      s.isEmpty() == (s.length == 0);
      @ also
      @   ensures \result <==>
      @      (new JMLObjectSequence(e1)).equals(
      @                  new JMLObjectSequence().insertFront(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLObjectSequence(e1)).equals(
      @                  new JMLObjectSequence().insertBack(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLObjectSequence(e1)).equals(
      @                  new JMLObjectSequence().insertAfterIndex(-1, e1));
      @ also
      @   ensures \result <==>
      @      (new JMLObjectSequence(e1)).equals(
      @                  new JMLObjectSequence().insertBeforeIndex(0, e1));
      @ also
      @   ensures \result <==>
      @      (s.size() >= 1 ==> s.equals(s.trailer().insertFront(s.first())));
      @ also
      @   ensures \result <==>
      @      (s.size() >= 1 ==> s.equals(s.header().insertBack(s.last())));
      @ also
      @   ensures \result <==>
      @      s.isProperSubsequence(s2)
      @            == ( s.isSubsequence(s2) && !s.equals(s2));
      @ also
      @   ensures \result <==>
      @      s.isSupersequence(s2) == s2.isSubsequence(s);
      @ also
      @   ensures \result <==>
      @      s.isProperSupersequence(s2) == s2.isProperSubsequence(s);
      @ |}
      @
      public pure model boolean equational_theory(JMLObjectSequence s,
                                                  JMLObjectSequence s2,
                                                  Object e1,
                                                  Object e2, \bigint n);
      @*/


    /*@ requires true;
      @ public static model pure BigInteger bigintToBigInteger(\bigint biValue);
      @*/


    /*@ public normal_behavior
      @ requires oBi.equals(BigInteger.ZERO);
      @ ensures \result == (\bigint)0;
      @ public static model pure \bigint bigIntegerToBigint(BigInteger oBi);
      @*/


    //@ public invariant elementType <: \type(Object);
    /*@ public invariant
      @           (\forall Object o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    //@ public invariant_redundantly isEmpty() ==> !containsNull;

    protected final JMLListObjectNode theSeq;
    //                                 in objectState;
    //@ invariant theSeq != null ==> theSeq.owner == this;

    protected final BigInteger _length;
    //                    in objectState;
    //@ public model \bigint length;
    //@ protected represents length <- bigIntegerToBigint(_length);

    //@ protected invariant theSeq == null <==> length == 0;
    //@ protected invariant length >= 0;
    
    /*@ protected invariant theSeq != null ==> length == theSeq.length();
      @  protected invariant length == length();
      @*/

    //@ public invariant owner == null;

    /*@  public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures isEmpty();
      @    ensures_redundantly size() == 0;
      @*/
    public JMLObjectSequence() {
        theSeq = null;
        _length = BigInteger.ZERO;
    }  

    /*@  public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures int_length() == 1;
      @    ensures (e == null ==> itemAt(0) == null)
      @         && (e != null ==> itemAt(0) == e); 
      @*/
    public JMLObjectSequence (Object e)
    {
        theSeq = JMLListObjectNode.cons(e, null); // cons() clones e, if needed
        _length = BigInteger.ONE;
    }

    /*@  public normal_behavior  
      @    requires ls == null <==> len == 0;
      @    requires len >= 0;
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures ls != null ==> elementType == ls.elementType;
      @    ensures ls != null ==> containsNull == ls.containsNull;
      @    ensures ls == null ==> elementType <: \type(Object);
      @    ensures ls == null ==> !containsNull;
    model protected JMLObjectSequence (JMLListObjectNode ls, \bigint len);
    @*/

    /** Initialize this sequence based on the given representation.
     */
    //@    requires ls == null <==> len == 0;
    //@    requires len >= 0;
    //@    assignable objectState, elementType, containsNull, owner;
    //@    ensures ls != null ==> elementType == ls.elementType;
    //@    ensures ls != null ==> containsNull == ls.containsNull;
    //@    ensures ls == null ==> elementType <: \type(Object);
    //@    ensures ls == null ==> !containsNull;
    protected JMLObjectSequence (JMLListObjectNode ls, int len) {
        theSeq = ls;	
        _length = BigInteger.valueOf(len);
    }

    //**************************** Static methods ****************************

    /** The empty JMLObjectSequence.
     *  @see #JMLObjectSequence()
     */
    public static final /*@ non_null @*/ JMLObjectSequence EMPTY
        = new JMLObjectSequence();

    /** Return the singleton sequence containing the given element.
     *  @see #JMLObjectSequence(Object)
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result != null && \result.equals(new JMLObjectSequence(e));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSequence singleton(Object e)
    {
        return new JMLObjectSequence(e);
    }

    /** Return the sequence containing all the elements in the given
     * array in the same order as the elements appear in the array.
     */
    /*@ public normal_behavior
      @    requires a != null;
      @    assignable \nothing;
      @    ensures \result != null && \result.size() == a.length
      @         && (\forall int i; 0 <= i && i < a.length;
      @                            (\result.itemAt(i) == null 
      @                               ? a[i] == null
      @                               : \result.itemAt(i) == a[i]));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSequence convertFrom(/*@ non_null @*/Object[] a)
    {
        /*@ non_null @*/ JMLObjectSequence ret = EMPTY;
        for (int i = a.length-1; 0 <= i; i--) {
            ret = ret.insertFront(a[i]);
        }
        return ret;
    } 

    /** Return the sequence containing the first 'size' elements in the given
     * array in the same order as the elements appear in the array.
     */
    /*@ public normal_behavior
      @    requires a != null && 0 <= size && size < a.length;
      @    assignable \nothing;
      @    ensures \result != null && \result.size() == size
      @         && (\forall int i; 0 <= i && i < size;
      @                            (\result.itemAt(i) == null 
      @                               ? a[i] == null
      @                               : \result.itemAt(i) == a[i]));
      @
      @ implies_that
      @    requires size < a.length;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSequence convertFrom(/*@ non_null @*/Object[] a, int size)
    {
        /*@ non_null @*/ JMLObjectSequence ret = EMPTY;
        for (int i = size-1; 0 <= i; i--) {
            ret = ret.insertFront(a[i]);
        }
        return ret;
    } 

    /** Return the sequence containing all the object in the
     *  given collection in the same order as the elements appear in the
     *  collection.
     *
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     *  @see #containsAll(java.util.Collection)
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && c.elementType <: \type(Object);
      @      requires c.size() < Integer.MAX_VALUE;
      @      assignable \nothing;
      @      ensures \result != null && \result.size() == c.size()
      @           && (\forall Object x; c.contains(x) <==> \result.has(x));
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.contains(o);
      @                                  !(o instanceof Object));
      @      assignable \nothing;
      @      signals (ClassCastException);
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSequence convertFrom(/*@ non_null @*/ java.util.Collection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLObjectSequence ret = EMPTY;
        java.util.Iterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insertBack(null);
            } else {
                ret = ret.insertBack(o);
            }
        }
        return ret;
    } 

    /** Return the sequence containing all the object in the
     *  given JMLCollection in the same order as the elements appear in the
     *  collection.
     *
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && c.elementType <: \type(Object);
      @      requires c.size() < Integer.MAX_VALUE;
      @      assignable \nothing;
      @      ensures \result != null
      @           && (\forall Object x; c.has(x) <==> \result.has(x));
      @      ensures_redundantly \result.size() == c.size();
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.has(o);
      @                                  !(o instanceof Object));
      @      assignable \nothing;
      @      signals (ClassCastException);
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSequence convertFrom(/*@ non_null @*/ JMLCollection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLObjectSequence ret = EMPTY;
        JMLIterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insertBack(null);
            } else {
                ret = ret.insertBack(o);
            }
        }
        return ret;
    } 

    //**************************** Observers **********************************

    /** Return the element at the given zero-based index.
     *  @param i the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index oBiI is out of range.
     *  @see #get(int)
     *  @see #has(Object)
     *  @see #count(Object)
     */
    /*@ // _ alsoIfValue _ //FIXME! later
      @  public normal_behavior
      @    requires 0 <= i && i < length;
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length);
      @    signals (JMLSequenceException);
    model public Object itemAt(\bigint i) throws JMLSequenceException;
    @*/

    /** Return the element at the given zero-based index.
     *  @param i the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index i is out of range.
     *  @see #get(int)
     *  @see #has(Object)
     *  @see #count(Object)
     *  @see #itemAt(\bigint)
     */
    /*@ 
      @  public normal_behavior
      @    requires 0 <= i && i < int_size();
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < int_size());
      @    signals (JMLSequenceException);
      @*/
    public Object itemAt(int i) throws JMLSequenceException {
        if (i < 0 || i >= int_length()) {
            throw new JMLSequenceException("Index out of range.");
        } else {
            JMLListObjectNode thisWalker = theSeq;
	      
            int k = 0;
            //@ loop_invariant 0 <= k && k <= i && thisWalker != null;
            for (; k < i; k++) {
                thisWalker = thisWalker.next;
            }   
            return (thisWalker.head());  // head() clones if necessary
        }
    }    

    /** Return the element at the given zero-based index; a synonym
     *  for {@link #itemAt}.
     *  @param i the zero-based index into the sequence.
     *  @exception IndexOutOfBoundsException if the index i is out of range.
     *  @see #itemAt(\bigint)
     */
    /*@  public normal_behavior
      @    requires 0 <= i && i < length; //FIXME, might use size();
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result "==" the ith element of this *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length); //FIXME, might use size());
      @    signals (IndexOutOfBoundsException);
      @
      @  model public Object get(\bigint i) throws IndexOutOfBoundsException ;
      @*/

    /** Return the element at the given zero-based index; a synonym
     *  for {@link #itemAt}.
     *  @param i the zero-based index into the sequence.
     *  @exception IndexOutOfBoundsException if the index i is out of range.
     *  @see #itemAt(int)
     */
    /*@  public normal_behavior
      @    requires 0 <= i && i < length;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length);
      @    signals (IndexOutOfBoundsException);
      @
      @*/
    public Object get(int i) throws IndexOutOfBoundsException {
        try {
            Object ret = itemAt(i);
            return ret;
        } catch (JMLSequenceException e) {
            IndexOutOfBoundsException e2 = new IndexOutOfBoundsException();
            e2.initCause(e);
            throw e2;
        }
    }  

    /*@
      @ public normal_behavior
      @  ensures \result == length;
      @ public model pure \bigint size();
      @*/

    /*@
      @ public normal_behavior
      @  ensures \result == length;
      @ public model pure \bigint length();
      @*/

    /*@ also
      @ protected normal_behavior
      @    requires size() <= Integer.MAX_VALUE;
      @    ensures \result == size();
      @
      @*/
    public int int_size( ) {
        return _length.intValue();
    }  

    /*@ 
      @    public normal_behavior
      @      requires size() <= Integer.MAX_VALUE;
      @      ensures \result == size();
      @*/
    public int int_length( ) {
        return _length.intValue();
    }  

    /*@
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of \bigint i; 0 <= i && i < length();
      @                             itemAt(i) != null
      @                             && itemAt(i) == item);
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of \bigint i; 0 <= i && i < length();
      @                                        itemAt(i) == null);
    model public \bigint bi_count(Object item);
    @*/

    /*@ 
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of int i; 0 <= i && i < int_length();
      @                             itemAt(i) != null
      @                             && itemAt(i) == item);
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of int i; 0 <= i && i < int_length();
      @                                        itemAt(i) == null);
      @*/
    public int count(Object item) {
        JMLListObjectNode ptr = this.theSeq;
        int cnt = 0;
        while (ptr != null) {
            if (ptr.headEquals(item)) {
                cnt++;
            }
            ptr = ptr.next;
        }
        return cnt;
    }

    /*@ also
      @   public normal_behavior
      @    {|
      @       requires elem != null;
      @       ensures \result <==> 
      @                 (\exists int i; 0 <= i && i < int_length();
      @                                 itemAt(i) == elem);
      @      also
      @       requires elem == null;
      @        ensures \result <==> 
      @                  (\exists int i; 0 <= i && i < int_length(); 
      @                                  itemAt(i) == null);
      @    |}
      @*/
    public boolean has(Object elem) {
        return theSeq != null && theSeq.has(elem);
    }  

    /*@ public normal_behavior
      @    requires c != null;
      @    ensures \result <==> (\forall Object o; c.contains(o); this.has(o));
      @*/
    public boolean containsAll(/*@ non_null @*/ java.util.Collection c) {
        java.util.Iterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (!has(o)) {
                return false;
            }
        }
        return true;
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @      int_length() <= s2.int_length()
      @      && (\forall int i; 0 <= i && i < int_length();
      @                   (s2.itemAt(i) != null 
      @                    && s2.itemAt(i) == (itemAt(i)))
      @                || (s2.itemAt(i) == null && itemAt(i) == null) );
      @*/
    public boolean isPrefix(/*@ non_null @*/ JMLObjectSequence s2) {
        return int_length() <= s2.int_length()
            && (theSeq == null || theSeq.isPrefixOf(s2.theSeq));
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isPrefix(s2) && !this.equals(s2);
      @*/
    public boolean isProperPrefix(/*@ non_null @*/ JMLObjectSequence s2) {
        return int_length() != s2.int_length() && isPrefix(s2);
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @       int_length() <= s2.int_length()
      @       && this.equals(s2.removePrefix(s2.int_length() - int_length()));
      @*/
    public boolean isSuffix(/*@ non_null @*/ JMLObjectSequence s2) {
        if (int_length() > s2.int_length()) {
            return false;
        } else if (int_length() == 0) {
            return true;
        } 
        JMLListObjectNode suffix = s2.theSeq.removePrefix(s2.int_length() - int_length());
        return theSeq.equals(suffix);
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isSuffix(s2) && !this.equals(s2);
      @*/
    public boolean isProperSuffix(/*@ non_null @*/ JMLObjectSequence s2) {
        return int_length() != s2.int_length() && isSuffix(s2);
    }  

    /** Test whether this object's value is equal to the given argument.
     *  @see #isSuffix
     *  @see #int_size()
     */
    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLObjectSequence;
      @     ensures \result <==>
      @          isPrefix((JMLObjectSequence)obj)
      @          && ((JMLObjectSequence)obj).isPrefix(this);
      @     ensures_redundantly \result ==>
      @          containsNull == ((JMLObjectSequence)obj).containsNull;
      @ also
      @  public normal_behavior
      @    requires obj == null || !(obj instanceof JMLObjectSequence);
      @    ensures !\result;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        return (obj != null && obj instanceof JMLObjectSequence)
            && (int_length() == ((JMLObjectSequence)obj).int_length())
            && isPrefix((JMLObjectSequence)obj);
    }  

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return (theSeq == null ? 0 : theSeq.hashCode());
    }

    /** Tells whether this sequence is empty.
     *  @see #int_size()
     *  @see #int_length()
     */
    /*@  public normal_behavior
      @    ensures \result == (int_length() == 0);
      @*/
    public /*@ pure @*/ boolean isEmpty() {
        return theSeq == null;
    }

    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures itemAt(\result) == item
      @             && (\forall \bigint i; 0 <= i && i < \result;
      @                                !(itemAt(i) == item));
      @       ensures_redundantly (* \result is the first index
      @                                at which item occurs in this *);
      @     also
      @      requires item == null;
      @      ensures itemAt(\result) == null
      @           && (\forall \bigint i; 0 <= i && i < \result;
      @                              itemAt(i) != null);
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires !has(item);
      @    signals (JMLSequenceException);
    model public \bigint bi_indexOf(Object item) throws JMLSequenceException ;
    @*/

    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures itemAt(\result) == item
      @             && (\forall int i; 0 <= i && i < \result;
      @                                !(itemAt(i) == item));
      @       ensures_redundantly (* \result is the first index
      @                                at which item occurs in this *);
      @     also
      @      requires item == null;
      @      ensures itemAt(\result) == null
      @           && (\forall int i; 0 <= i && i < \result;
      @                              itemAt(i) != null);
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires !has(item);
      @    signals (JMLSequenceException);
      @*/
    public int indexOf(Object item) throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException(ITEM_PREFIX + item + IS_NOT_FOUND);
        }
        int idx = theSeq.indexOf(item);
        if (idx == -1) {
            throw new JMLSequenceException(ITEM_PREFIX + item + IS_NOT_FOUND);
        } else {
            return idx;
        }
    }

    private static final String ITEM_PREFIX = "item ";
    private static final String IS_NOT_FOUND = " is not in this sequence.";

    /*@ 
      @  public normal_behavior
      @    requires int_length() > 0;
      @    {|
      @       requires itemAt(0) != null;
      @       ensures \result == (itemAt(0));
      @      also
      @       requires itemAt(0) == null;
      @       ensures \result == null;
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @*/
    public /*@ pure @*/ Object first() throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried first() on empty sequence.");
        } else {
            return (theSeq.head());  // head() clones if necessary
        }   
    }

    /*@ 
      @  public normal_behavior
      @    requires int_length() >= 1;
      @    {|
      @       requires itemAt((int)(int_length()-1)) != null;
      @       ensures \result == (itemAt((int)(int_length()-1)));
      @     also
      @       requires itemAt((int)(int_length()-1)) == null;
      @       ensures \result == null;
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @*/
    public Object last() throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried last() on empty sequence.");
        } else {
            return theSeq.last();  // last() clones if necessary
        }   
    }

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @                 int_length() <= s2.int_length()
      @              && (\exists int i; 0 <= i && i < s2.int_length()-int_length()+1;
      @                                 isPrefix(s2.removePrefix(i)));
      @*/
    public boolean isSubsequence(/*@ non_null @*/ JMLObjectSequence s2) {
        JMLListObjectNode walker = s2.theSeq;
        for (int walkerLen = s2.int_length(); int_length() <= walkerLen; walkerLen--) {
            if (theSeq == null || theSeq.isPrefixOf(walker)) {
                return true;
            }
            walker = walker.next;
        }   
        return false;
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @        this.isSubsequence(s2) && !this.equals(s2);
      @*/
    public boolean isProperSubsequence(/*@ non_null @*/ JMLObjectSequence s2) {
        return int_length() < s2.int_length() && isSubsequence(s2);
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isSubsequence(this);
      @*/
    public boolean isSupersequence(/*@ non_null @*/ JMLObjectSequence s2) {
        return s2.isSubsequence(this);
    }

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isProperSubsequence(this);
      @*/
    public
        boolean isProperSupersequence(/*@ non_null @*/ JMLObjectSequence s2) {
        return s2.isProperSubsequence(this);
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < int_length();
      @                         itemAt(i) == elem
      @                         && subsequence(0,i)
      @                            .concat(subsequence((int)(i+1),int_length()))
      @                            .equals(s2));
      @    ensures_redundantly \result ==> this.int_length() == s2.int_length()+1;
      @    ensures_redundantly \result ==> has(elem);
      @    ensures_redundantly \result <==> s2.isDeletionFrom(this, elem);
      @*/
    public boolean isInsertionInto(/*@ non_null @*/ JMLObjectSequence s2,
                                   Object elem) {
        if (int_length() != s2.int_length() + 1) {
            return false;
        }
        JMLListObjectNode walker = theSeq;
        JMLListObjectNode s2walker = s2.theSeq;
	int lenRemaining;
        /*@ maintaining subsequence(0, (int)(int_length()-lenRemaining))
          @                 .equals(s2.subsequence(0, (int)(int_length()-lenRemaining)));
          @ decreasing int_length();
          @*/
        for (lenRemaining = int_length(); lenRemaining > 0; lenRemaining--) {
            if (walker.headEquals(elem)) {
                if ((walker.next == null && s2walker == null)
                    || (walker.next != null && walker.next.equals(s2walker))) {
                    return true;
                }
            }
            if (s2walker == null || !s2walker.headEquals(walker.head())) {
                return false;
            }
            walker = walker.next;
            s2walker = s2walker.next;
        }   
        return false;
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < s2.int_length();
      @                         s2.itemAt(i) == elem
      @                         && this.equals(s2.removeItemAt(i)));
      @    ensures_redundantly \result ==> this.int_length()+1 == s2.int_length();
      @    ensures_redundantly \result ==> s2.has(elem);
      @    ensures_redundantly \result <==> s2.isInsertionInto(this, elem);
      @*/
    public boolean isDeletionFrom(/*@ non_null @*/ JMLObjectSequence s2,
                                  Object elem) {
        return s2.isInsertionInto(this, elem);
    }  

    // *************** building new JMLObjectSequences **********************

    /** Return a clone of this object.  This method does not clone the
     * elements of the sequence.
     */
    /*@ also
      @  public normal_behavior
      @   ensures \result != null
      @        && \result instanceof JMLObjectSequence
      @        && ((JMLObjectSequence)\result).equals(this);
      @*/
    public Object clone() { 
        return this;
    }  

    /** Return a sequence containing the first n elements in this sequence.
     *  @param n the number of elements in the result.
     *  @exception JMLSequenceException if n is negative or greater than
     *  the length of the sequence.
     * @see #trailer
     * @see #removePrefix
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == n
      @            && (\forall \bigint i; 0 <= i && i < n;
      @                   (\result.itemAt(i) != null 
      @                    ==> \result.itemAt(i) == (itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @
      @ implies_that
      @    ensures !containsNull ==> !\result.containsNull;
      @
      model public JMLObjectSequence prefix(\bigint n) throws JMLSequenceException;
      @*/

    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == n
      @            && (\forall int i; 0 <= i && i < n;
      @                   (\result.itemAt(i) != null 
      @                    ==> \result.itemAt(i) == (itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @
      @*/
      public /*@ non_null @*/ JMLObjectSequence prefix(int n)
	  throws JMLSequenceException {
	  if (n < 0 || n > int_length()) {
	      throw new
		  JMLSequenceException("Invalid parameter to prefix() with n = " 
				       + n + "\n"
				       + "   when sequence length = " + int_length());
	  } else {
	      if (n == 0) {
		  return new JMLObjectSequence();
	      } else {
		  JMLListObjectNode pfx_list = theSeq.prefix(n);
		  return new JMLObjectSequence(pfx_list, n);
	      }
	  }
      }  

    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt(i-n) != null 
      @                   && \result.itemAt(i-n) == (itemAt(i)))
      @               || (\result.itemAt(i-n) == null 
      @                   && itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      model public JMLObjectSequence removePrefix(\bigint n) throws JMLSequenceException ;
      @*/  

    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt((int)(i-n)) != null 
      @                   && \result.itemAt((int)(i-n)) == (itemAt(i)))
      @               || (\result.itemAt((int)(i-n)) == null 
      @                   && itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ JMLObjectSequence removePrefix(int n)
        throws JMLSequenceException {
        if (n < 0 || n > int_length()) {
            throw new
                JMLSequenceException("Invalid parameter to removePrefix() "
                                     + "with n = " + n + "\n"
                                     + "   when sequence length = " + int_length());
        } else {
            if (n == 0) {
                return this;
            } else {
                JMLListObjectNode pfx_list = theSeq.removePrefix(n);
                return new JMLObjectSequence(pfx_list, int_length()-n);
            }
        }
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result.int_length() == int_length() + s2.int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                   (\result.itemAt(i) != null 
      @                    && \result.itemAt(i) == (itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    && itemAt(i) == null) )
      @         && (\forall int i; 0 <= i && i < s2.int_length();
      @                   (\result.itemAt((int)(int_length()+i)) != null 
      @                    && \result.itemAt((int)(int_length()+i)) == (s2.itemAt(i)))
      @                || (\result.itemAt((int)(int_length()+i)) == null 
      @                    && s2.itemAt(i) == null) );
      @*/
    public /*@ non_null @*/
        JMLObjectSequence concat(/*@ non_null @*/ JMLObjectSequence s2) {
        if (theSeq == null) {
            return s2;
        } else if (s2.theSeq == null) {
            return this;
        } else {
            JMLListObjectNode new_list = theSeq.concat(s2.theSeq);
	    return new JMLObjectSequence(new_list,
                                         int_length() + s2.int_length());
        }
    }

    /*@  public normal_behavior
      @    old int len = int_length();
      @    ensures \result.int_length() == len
      @         && (\forall int i; 0 <= i && i < len;
      @                   (\result.itemAt((int)(len-i-1)) != null 
      @                    && \result.itemAt((int)(len-i-1)) == (itemAt(i)))
      @                || (\result.itemAt((int)(len-i-1)) == null 
      @                    && itemAt(i) == null) );
      @*/
    public /*@ non_null @*/ JMLObjectSequence reverse() {
        if (theSeq == null) {
            return this;
        } else {
            JMLListObjectNode r = theSeq.reverse();
            return new JMLObjectSequence(r, int_length());
        }
    } 

    /*@  public normal_behavior
      @    requires 0 <= index && index < length();
      @    ensures \result.equals(prefix(index).concat(removePrefix(index+1)));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals (JMLSequenceException);
      @
    model public  non_null  JMLObjectSequence removeItemAt(\bigint index)
        throws JMLSequenceException ;
    @*/

    /*@  public normal_behavior
      @    requires 0 <= index && index < int_length();
      @    ensures \result.equals(prefix(index).concat(removePrefix((int)(index+1))));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < int_length());
      @    signals (JMLSequenceException);
      @
      @*/
    public /*@ non_null @*/ JMLObjectSequence removeItemAt(int index)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            JMLListObjectNode new_list = theSeq.removeItemAt(index);
            return new JMLObjectSequence(new_list, int_length()-1);
        } else {
            throw new
                JMLSequenceException("Invalid parameter to removeItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + int_length());
        }
    }

    /*@  public normal_behavior
      @    requires 0 <= index && index < length();
      @    ensures \result.equals(removeItemAt(index).insertBeforeIndex(index,
      @                                                                 item));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals (JMLSequenceException);
    model public  non_null  JMLObjectSequence replaceItemAt(\bigint index, Object item) throws JMLSequenceException;
    @*/

    /*@  public normal_behavior
      @    requires 0 <= index && index < int_length();
      @    ensures \result.equals(removeItemAt(index).insertBeforeIndex(index,
      @                                                                 item));
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with item replacing the one at position index *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < int_length());
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ JMLObjectSequence
        replaceItemAt(int index, Object item)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            JMLListObjectNode new_list = theSeq.replaceItemAt(index, item);
            return new JMLObjectSequence(new_list, int_length());
        } else {
            throw new
                JMLSequenceException("Invalid parameter to replaceItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + int_length());
        }
    }

    /*@  public normal_behavior
      @    requires int_length() >= 1;
      @    ensures \result.equals(removeItemAt((int)(int_length()-1)));
      @    ensures_redundantly \result.int_length() == int_length() - 1
      @          && (* \result is like this, but without the last item *);
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @
      @*/
    public /*@ non_null @*/ JMLObjectSequence header()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried header() on empty sequence.");
        } else {
            JMLListObjectNode new_list = theSeq.removeLast();
            return new JMLObjectSequence(new_list, int_length() - 1);
        }   
    }

    /*@  public normal_behavior
      @    requires int_length() >= 1;
      @    ensures \result.equals(removePrefix(1));
      @    ensures_redundantly \result.int_length() == int_length() - 1
      @           && (* \result is like this, but without the first item *);
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @
      @*/
    public /*@ pure @*/ /*@ non_null @*/ JMLObjectSequence trailer()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried trailer() on empty sequence.");
        } else {
            JMLListObjectNode new_list = theSeq.next;
            return new JMLObjectSequence(new_list, int_length() - 1);
        }   
    }  


    /*@ //FIXME, _ alsoIfValue _
      @  public normal_behavior
      @    requires -1 <= afterThisOne && afterThisOne < length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex((int)(afterThisOne + 1), item));
      @    ensures_redundantly 
      @          (* \result is the same sequence as this,
      @             but with item inserted after the index "afterThisOne" *);
      @ also
      @  public exceptional_behavior
      @    requires !(-1 <= afterThisOne && afterThisOne < length);
      @    signals (JMLSequenceException);
      model public JMLObjectSequence insertAfterIndex(\bigint afterThisOne, Object item) throws JMLSequenceException, IllegalStateException;
      @*/


    /*@ 
      @  public normal_behavior
      @    requires -1 <= afterThisOne && afterThisOne < length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex((int)(afterThisOne + 1), item));
      @ also
      @  public exceptional_behavior
      @    requires !(-1 <= afterThisOne && afterThisOne < length);
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ JMLObjectSequence insertAfterIndex(int afterThisOne,
                                                             Object item)
        throws JMLSequenceException, IllegalStateException
    {
        if (afterThisOne < -1 || afterThisOne >= int_length()) {
            throw new JMLSequenceException("Invalid parameter to "
                                           + "insertAfterIndex() "
                                           + "with afterThisOne = " 
                                           + afterThisOne + "\n"
                                           + "   when sequence length = "
                                           + int_length());
        } else if (int_length() < Integer.MAX_VALUE) {
            return insertBeforeIndex(afterThisOne+1, item);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }


    private static final String TOO_BIG_TO_INSERT
        = "Cannot insert into a sequence with Integer.MAX_VALUE elements.";

    /*@ 
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLObjectSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      model public  
        JMLObjectSequence insertBeforeIndex(\bigint beforeThisOne, Object item)
        throws JMLSequenceException, IllegalStateException;
	@*/

    /*@ 
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLObjectSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ 
        JMLObjectSequence insertBeforeIndex(int beforeThisOne, Object item)
        throws JMLSequenceException, IllegalStateException
    {
        if (beforeThisOne < 0 || beforeThisOne > int_length()) {
            throw new
                JMLSequenceException("Invalid parameter to insertBeforeIndex()"
                                     + " with beforeThisOne = " 
                                     + beforeThisOne + "\n"
                                     + "   when sequence length = " + int_length());
        } else if (int_length() < Integer.MAX_VALUE) {
            if (theSeq == null) {
                return new JMLObjectSequence(item);
            } else {
                // insertBefore() clones item, if necessary
                JMLListObjectNode new_list
                    = theSeq.insertBefore(beforeThisOne, item);
                return new JMLObjectSequence(new_list, int_length()+1);
            }
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    } 

    /*@ 
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(int_length(), item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && isProperPrefix(\result);
      @*/
    public /*@ non_null @*/ JMLObjectSequence insertBack(Object item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLObjectSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            return new JMLObjectSequence(theSeq.append(item), int_length()+1);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }

    /*@ 
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(0, item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && \result.trailer().equals(this);
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and item is d *);
      @     ensures (* \result is <d,a,b,c> *);
      @*/
    public /*@ pure @*/ /*@ non_null @*/ JMLObjectSequence insertFront(Object item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLObjectSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            return new JMLObjectSequence(  // cons() clones item, if necessary
                                         JMLListObjectNode.cons(item, theSeq),
                                         int_length()+1);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }

    /*@  public normal_behavior
      @    requires 0 <= from && from <= to && to <= length();
      @    ensures \result.equals(removePrefix(from).prefix((int)(to - from)));
      @    ensures_redundantly
      @           (* \result contains the elements of this beginning with
      @              index from (inclusive) and ending
      @              with index to (exclusive) *)
      @         && \result.length() == to - from;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= from && from <= to && to <= length());
      @    signals (JMLSequenceException);
      @
      model public  non_null  JMLObjectSequence subsequence(\bigint from, \bigint to) throws JMLSequenceException ;
      @*/

    /*@  public normal_behavior
      @    requires 0 <= from && from <= to && to <= int_length();
      @    ensures \result.equals(removePrefix(from).prefix((int)(to - from)));
      @    ensures_redundantly
      @           (* \result contains the elements of this beginning with
      @              index from (inclusive) and ending
      @              with index to (exclusive) *)
      @         && \result.int_length() == to - from;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= from && from <= to && to <= int_length());
      @    signals (JMLSequenceException);
      @
      @*/
    public /*@ non_null @*/ JMLObjectSequence subsequence(int from, int to)
        throws JMLSequenceException {
        if (from < 0 || from > to || to > int_length()) {
            throw new JMLSequenceException("Invalid parameters to "
                                           + "subsequence() with from = " 
                                           + from + " and to = " + to + "\n"
                                           + "   " + "when sequence length = "
                                           + int_length());
        } else {
            if (theSeq == null) {
                return this;  
            } else {
                JMLListObjectNode removedPrefix = theSeq.removePrefix(from);
                if (removedPrefix == null) {
                    return new JMLObjectSequence();
                } else {
                    JMLListObjectNode new_list = removedPrefix.prefix(to-from);
                    return new JMLObjectSequence(new_list, to - from);
                }
            }
        }
    }

    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall int i; 0 <= i && i < int_length();
      @                            \result.count(this.itemAt(i))
      @                             == this.count(this.itemAt(i)));
      @*/
    public /*@ non_null @*/ JMLObjectBag toBag() {
        JMLObjectBag ret = new JMLObjectBag();
        JMLObjectSequenceEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            Object e = (o == null ? null :  o);
            ret = ret.insert(e);
        }
        return ret;
    } 

    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall Object o;; \result.has(o) == this.has(o));
      @*/
    public /*@ non_null @*/ JMLObjectSet toSet() {
        JMLObjectSet ret = new JMLObjectSet();
        JMLObjectSequenceEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            Object e = (o == null ? null :  o);
            ret = ret.insert(e);
        }
        return ret;
    } 

    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                 (\result[i] == null ==> this.itemAt(i) == null)
      @              && (\result[i] != null ==>
      @                   \result[i] == (this.itemAt(i))));
      @*/
    public /*@ non_null @*/ Object[] toArray() {
        Object[] ret = new Object[int_length()];
        JMLObjectSequenceEnumerator enum = elements();
        int i = 0;
        //@ loop_invariant 0 <= i && i <= ret.length;
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            if (o == null) {
                ret[i] = null;
            } else {
                Object e =  o;
                ret[i] =  e ;
            }
            i++;
        }
        return ret;
    }

    /*@  public normal_behavior
      @    ensures \fresh(\result);
      @*/
    public /*@ non_null @*/ JMLObjectSequenceEnumerator elements() {
        JMLObjectSequenceEnumerator retValue 
            = new JMLObjectSequenceEnumerator(this);
        return retValue;
    }  

    /*@ also
      @    public normal_behavior
      @      ensures \fresh(\result)
      @          && \result.equals(new JMLEnumerationToIterator(elements()));
      @*/  
    public JMLIterator iterator() {
        return new JMLEnumerationToIterator(elements());
    }  

    public String toString() {
        String newStr = "(<";
        JMLListObjectNode seqWalker = theSeq;
        boolean first = true;
        while (seqWalker != null) {
            if (!first) {
                newStr = newStr + ", ";
            }
            newStr = newStr + seqWalker.val;
            first = false;
            seqWalker = seqWalker.next;
        }
        return(newStr + ">)");
    }


}
