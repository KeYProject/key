// @(#)$Id: JMLEqualsSequence.java 1.3 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

public /*@ pure @*/ class JMLEqualsSequence
    implements JMLCollection
{

    //*********************** equational theory ***********************

    /*@ public invariant (\forall JMLEqualsSequence s2;
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
      @    ensures \result <==> !(new JMLEqualsSequence()).has(e1);
      @  also
      @    ensures \result <==> (new JMLEqualsSequence()).size() == 0;
      @  also
      @    ensures \result <==> (new JMLEqualsSequence(e1)).size() == 1;
      @  also
      @    ensures \result <==> 
      @        e1 != null ==>
      @        (new JMLEqualsSequence(e1)).itemAt(0) .equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).first() .equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).last() .equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).itemAt(0) .equals(e1);
      @  also
      @    ensures \result <==>
      @        s.insertFront(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).itemAt(s.size()) .equals(e1);
      @  also
      @    ensures \result <==>
      @        s.insertBack(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==> 
      @    // !FIXME! The following may be inconsistent: argument to itemAt might
      @    // be equal to size, but it is required to be less than size.
      @        -1 <= n && n < s.size() && e1 != null
      @          ==> s.insertAfterIndex(n, e1).itemAt(n+1) .equals(e1);
      @  also
      @    ensures \result <==> 
      @        -1 <= n && n < s.size()
      @          ==> s.insertAfterIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        0 <= n && n <= s.size() && e1 != null
      @          ==> s.insertBeforeIndex(n, e1).itemAt(n) .equals(e1);
      @  also
      @    ensures \result <==> 
      @        0 <= n && n <= s.size()
      @          ==> s.insertBeforeIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        s.isPrefix(s2)
      @           == (\forall int i; 0 <= i && i < s.int_length();
      @                  (s2.itemAt(i) != null 
      @                   && s2.itemAt(i) .equals(s.itemAt(i)))
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
      @      (new JMLEqualsSequence(e1)).equals(
      @                  new JMLEqualsSequence().insertFront(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLEqualsSequence(e1)).equals(
      @                  new JMLEqualsSequence().insertBack(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLEqualsSequence(e1)).equals(
      @                  new JMLEqualsSequence().insertAfterIndex(-1, e1));
      @ also
      @   ensures \result <==>
      @      (new JMLEqualsSequence(e1)).equals(
      @                  new JMLEqualsSequence().insertBeforeIndex(0, e1));
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
      public pure model boolean equational_theory(JMLEqualsSequence s,
                                                  JMLEqualsSequence s2,
                                                  Object e1,
                                                  Object e2, \bigint n);
      @*/

    //exchange a value of a \bigint to BigInteger
    /*@
      @  public normal_behavior
      @    ensures true;
      @     public static model pure BigInteger bigintToBigInteger(\bigint biValue);
      @*/

    //exchange a value of a BigInteger to \bigint
    /*@ public normal_behavior
         requires oBi.equals(BigInteger.ZERO);
         ensures \result == (\bigint)0;
      @ public static model pure \bigint bigIntegerToBigint(BigInteger oBi);
      @*/


    //@ public invariant elementType <: \type(Object);
    /*@ public invariant
      @           (\forall Object o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    //@ public invariant_redundantly isEmpty() ==> !containsNull;

    /** The list representing this sequence's elements, in order.
     */
    protected final JMLListEqualsNode theSeq;
    //@                                 in objectState;
    //@ invariant theSeq != null ==> theSeq.owner == this;

    /** This sequence's length.
     */
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

    //************************* Constructors ********************************

    /** Initialize this to be the empty sequence.
     *  @see #EMPTY
     */
    /*@  public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures isEmpty();
      @    ensures_redundantly size() == 0;
      @*/
    public JMLEqualsSequence() {
        theSeq = null;
        _length = BigInteger.ZERO;
    }  

    /** Initialize this to be the sequence containing just the given element.
     *  @param e the element that is the first element in this sequence.
     *  @see #singleton
     */
    public JMLEqualsSequence (Object e)
        /*@  public normal_behavior
          @    assignable objectState, elementType, containsNull, owner;
          @    ensures int_length() == 1;
          @    ensures (e == null ==> itemAt(0) == null)
          @         && (e != null ==> itemAt(0) .equals(e)); 
          @*/
    {
        theSeq = JMLListEqualsNode.cons(e, null); // cons() clones e, if needed
        _length = BigInteger.ONE;
    }

    /** Initialize this sequence based on the given representation.
     */
    /*@    requires ls == null <==> len == 0;
      @    requires len >= 0;
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures ls != null ==> elementType == ls.elementType;
      @    ensures ls != null ==> containsNull == ls.containsNull;
      @    ensures ls == null ==> elementType <: \type(Object);
      @    ensures ls == null ==> !containsNull;
    
    model protected JMLEqualsSequence (JMLListEqualsNode ls, \bigint len);
    @*/
    

    /** Initialize this sequence based on the given representation.
     */
    /*@    requires ls == null <==> len == 0;
      @    requires len >= 0;
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures ls != null ==> elementType == ls.elementType;
      @    ensures ls != null ==> containsNull == ls.containsNull;
      @    ensures ls == null ==> elementType <: \type(Object);
      @    ensures ls == null ==> !containsNull;
      @*/
    protected JMLEqualsSequence (JMLListEqualsNode ls, int len) {
        theSeq = ls;	
        _length = BigInteger.valueOf(len);
    }

    //**************************** Static methods ****************************

    /** The empty JMLEqualsSequence.
     *  @see #JMLEqualsSequence()
     */
    public static final /*@ non_null @*/ JMLEqualsSequence EMPTY
        = new JMLEqualsSequence();

    /** Return the singleton sequence containing the given element.
     *  @see #JMLEqualsSequence(Object)
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result != null && \result.equals(new JMLEqualsSequence(e));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLEqualsSequence singleton(Object e)
    {
        return new JMLEqualsSequence(e);
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
      @                               : \result.itemAt(i) .equals(a[i])));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLEqualsSequence convertFrom(/*@ non_null @*/Object[] a)
    {
        /*@ non_null @*/ JMLEqualsSequence ret = EMPTY;
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
      @                               : \result.itemAt(i) .equals(a[i])));
      @
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLEqualsSequence convertFrom(/*@ non_null @*/Object[] a, int size)
    {
        /*@ non_null @*/ JMLEqualsSequence ret = EMPTY;
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
        JMLEqualsSequence convertFrom(/*@ non_null @*/ java.util.Collection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLEqualsSequence ret = EMPTY;
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
        JMLEqualsSequence convertFrom(/*@ non_null @*/ JMLCollection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLEqualsSequence ret = EMPTY;
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
    /*@ 
      @  public normal_behavior
      @    requires 0 <= i && i < length;
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length);
      @    signals (JMLSequenceException);
    model public Object itemAt(\bigint i) throws JMLSequenceException {
        if (i < 0 || i >= this.length) {
            throw new JMLSequenceException("Index out of range.");
        } else {
            JMLListEqualsNode thisWalker = theSeq;
	  
            \bigint k = 0;
            loop_invariant 0 <= k && k <= i && thisWalker != null;
            for (; k < i; k=k+1) {
                assume thisWalker.next != null;
                thisWalker = thisWalker.next;
            }   
            return (thisWalker.head());  // head() clones if necessary
        }
    }    
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
            JMLListEqualsNode thisWalker = theSeq;
	      
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
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length); //FIXME, might use size());
      @    signals (IndexOutOfBoundsException);
      @
      model public Object get(\bigint i) throws IndexOutOfBoundsException;
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

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #length}.
     * @see #length()
     * @see #isEmpty()
     */
    /*@
      @ public normal_behavior
      @   ensures \result == length;
      @ public model pure \bigint size() {
      @   return length;
      @ } 
      @*/

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #length}.
     * @see #size()
     * @see #isEmpty()
     */
    /*@
      @ public normal_behavior
      @   ensures \result == length;
      @ public model pure \bigint length();
      @*/

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #length}.
     * @see #length()
     * @see #isEmpty()
     */
    /*@ also
      @ protected normal_behavior
      @    requires size() <= Integer.MAX_VALUE;
      @    ensures \result == size();
      @
      @*/
    public int int_size( ) {
        return _length.intValue();
    }  

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #size}.
     * @see #int_size()
     */
    /*@ 
      @    public normal_behavior
      @      requires size() <= Integer.MAX_VALUE;
      @      ensures \result == size();
      @*/
    public int int_length( ) {
        return _length.intValue();
    }  

    /** Tells the number of times a given element occurs in the sequence.
     *  @see #has(Object)
     *  @see #itemAt(int)
     */
    /*@ // //FIXME, remove // later
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of \bigint i; 0 <= i && i < length();
      @                             itemAt(i) != null
      @                             && itemAt(i) .equals(item));
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of \bigint i; 0 <= i && i < length();
      @                                        itemAt(i) == null);
    model public \bigint bi_count(Object item);
    @*/

    /** Tells the number of times a given element occurs in the sequence.
     *  @see #has(Object)
     *  @see #itemAt(int)
     */
    /*@ 
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of int i; 0 <= i && i < int_length();
      @                             itemAt(i) != null
      @                             && itemAt(i) .equals(item));
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of int i; 0 <= i && i < int_length();
      @                                        itemAt(i) == null);
      @*/
    public int count(Object item) {
        JMLListEqualsNode ptr = this.theSeq;
        int cnt = 0;
        while (ptr != null) {
            if (ptr.headEquals(item)) {
                cnt++;
            }
            ptr = ptr.next;
        }
        return cnt;
    }

    /** Tells whether the given element is ".equals" to an
     * element in the sequence.
     * @see #count(Object)
     */
    /*@ also
      @   public normal_behavior
      @    {|
      @       requires elem != null;
      @       ensures \result <==> 
      @                 (\exists int i; 0 <= i && i < int_length();
      @                                 itemAt(i) .equals(elem));
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

    /** Tell whether, for each element in the given collection, there is a
     * ".equals" element in this sequence.
     *  @param c the collection whose elements are sought.
     */
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

    /** Tells whether the elements of the this sequence occur, in
     * order, at the beginning of the given sequence, using
     * ".equals" for comparisons.
     *  @see #isProperPrefix
     *  @see #isSuffix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @      int_length() <= s2.int_length()
      @      && (\forall int i; 0 <= i && i < int_length();
      @                   (s2.itemAt(i) != null 
      @                    && s2.itemAt(i) .equals(itemAt(i)))
      @                || (s2.itemAt(i) == null && itemAt(i) == null) );
      @*/
    public boolean isPrefix(/*@ non_null @*/ JMLEqualsSequence s2) {
        return int_length() <= s2.int_length()
            && (theSeq == null || theSeq.isPrefixOf(s2.theSeq));
    }  

    /** Tells whether this sequence is shorter than the given
     *  sequence, and also if the elements of this sequence occur, in
     *  order, at the beginning of the given sequence, using
     *  ".equals" for comparisons.
     *  @see #isPrefix
     *  @see #isProperSuffix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isPrefix(s2) && !this.equals(s2);
      @*/
    public boolean isProperPrefix(/*@ non_null @*/ JMLEqualsSequence s2) {
        return int_length() != s2.int_length() && isPrefix(s2);
    }  

    /** Tells whether the elements of this sequence occur, in order,
     *  at the end of the given sequence, using ".equals" for
     *  comparisons.
     *  @see #isProperSuffix
     *  @see #isPrefix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @       int_length() <= s2.int_length()
      @       && this.equals(s2.removePrefix(s2.int_length() - int_length()));
      @*/
    public boolean isSuffix(/*@ non_null @*/ JMLEqualsSequence s2) {
        if (int_length() > s2.int_length()) {
            return false;
        } else if (int_length() == 0) {
            return true;
        } 
        JMLListEqualsNode suffix = s2.theSeq.removePrefix(s2.int_length() - int_length());
        return theSeq.equals(suffix);
    }  

    /** Tells whether the this sequence is shorter than the given
     *  object, and also if the elements of this sequence occur, in
     *  order, at the end of the given sequence, using
     *  ".equals" for comparisons.
     *  @see #isSuffix
     *  @see #isProperPrefix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isSuffix(s2) && !this.equals(s2);
      @*/
    public boolean isProperSuffix(/*@ non_null @*/ JMLEqualsSequence s2) {
        return int_length() != s2.int_length() && isSuffix(s2);
    }  

    /** Test whether this object's value is equal to the given argument.
     *  @see #isSuffix
     *  @see #int_size()
     */
    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLEqualsSequence;
      @     ensures \result <==>
      @          isPrefix((JMLEqualsSequence)obj)
      @          && ((JMLEqualsSequence)obj).isPrefix(this);
      @     ensures_redundantly \result ==>
      @          containsNull == ((JMLEqualsSequence)obj).containsNull;
      @ also
      @  public normal_behavior
      @    requires obj == null || !(obj instanceof JMLEqualsSequence);
      @    ensures !\result;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        return (obj != null && obj instanceof JMLEqualsSequence)
            && (int_length() == ((JMLEqualsSequence)obj).int_length())
            && isPrefix((JMLEqualsSequence)obj);
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

    /** Return the zero-based index of the first occurrence of the given
     *  element in the sequence, if there is one
     * @param item the Object sought in this.
     * @return the first index at which item occurs.
     * @exception JMLSequenceException if item is not a member of the sequence.
     * @see #itemAt(int)
     */
    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures itemAt(\result) .equals(item)
      @             && (\forall \bigint i; 0 <= i && i < \result;
      @                                !(itemAt(i) .equals(item)));
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
      @
    model public \bigint bi_indexOf(Object item) throws JMLSequenceException ;
    @*/

    /** Return the zero-based index of the first occurrence of the given
     *  element in the sequence, if there is one
     * @param item the Object sought in this.
     * @return the first index at which item occurs.
     * @exception JMLSequenceException if item is not a member of the sequence.
     * @see #itemAt(int)
     */
    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures itemAt(\result) .equals(item)
      @             && (\forall int i; 0 <= i && i < \result;
      @                                !(itemAt(i) .equals(item)));
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

    /** Return the first element in this sequence.
     *  @exception JMLSequenceException if the sequence is empty.
     * @see #itemAt(int)
     * @see #last
     * @see #trailer
     * @see #header
     */
    /*@ 
      @  public normal_behavior
      @    requires int_length() > 0;
      @    {|
      @       requires itemAt(0) != null;
      @       ensures \result .equals(itemAt(0));
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

    /** Return the last element in this sequence.
     *  @exception JMLSequenceException if the sequence is empty.
     * @see #itemAt(int)
     * @see #first
     * @see #header
     * @see #trailer
     */
    /*@ 
      @  public normal_behavior
      @    requires int_length() >= 1;
      @    {|
      @       requires itemAt((int)(int_length()-1)) != null;
      @       ensures \result .equals(itemAt((int)(int_length()-1)));
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

    /** Tells whether this sequence is a subsequence of the given sequence.
     *  @param s2 the sequence to search for within this sequence.
     *  @return whether the elements of this occur (in order) within s2.
     * @see #isProperSubsequence
     * @see #isSupersequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @                 int_length() <= s2.int_length()
      @              && (\exists int i; 0 <= i && i < s2.int_length()-int_length()+1;
      @                                 isPrefix(s2.removePrefix(i)));
      @*/
    public boolean isSubsequence(/*@ non_null @*/ JMLEqualsSequence s2) {
        JMLListEqualsNode walker = s2.theSeq;
        for (int walkerLen = s2.int_length(); int_length() <= walkerLen; walkerLen--) {
            if (theSeq == null || theSeq.isPrefixOf(walker)) {
                return true;
            }
            walker = walker.next;
        }   
        return false;
    }  

    /** Tells whether this sequence is strictly shorter than the given
     *  sequence and a subsequence of it.
     *  @param s2 the sequence to search for within this sequence.
     *  @return whether the elements of s2 occur (in order) within this.
     * @see #isSubsequence
     * @see #isProperSupersequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @        this.isSubsequence(s2) && !this.equals(s2);
      @*/
    public boolean isProperSubsequence(/*@ non_null @*/ JMLEqualsSequence s2) {
        return int_length() < s2.int_length() && isSubsequence(s2);
    }  

    /** Tells whether the given sequence is a supersequence of this sequence.
     *  @param s2 the sequence to search within for this sequence.
     *  @return whether the elements of this occur (in order) within s2.
     * @see #isProperSubsequence
     * @see #isSubsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isSubsequence(this);
      @*/
    public boolean isSupersequence(/*@ non_null @*/ JMLEqualsSequence s2) {
        return s2.isSubsequence(this);
    }

    /** Tells whether the given sequence is both longer than and a
     *  supersequence of this sequence.
     *  @param s2 the sequence to search within for this sequence.
     *  @return whether the elements of this occur (in order) within s2.
     * @see #isSupersequence
     * @see #isProperSubsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isProperSubsequence(this);
      @*/
    public
        boolean isProperSupersequence(/*@ non_null @*/ JMLEqualsSequence s2) {
        return s2.isProperSubsequence(this);
    }  

    /** Tells whether this sequence is the result of inserting the
     *  given element once into the given sequence.  That is, this
     *  sequence is exactly one element longer than the given
     *  sequence, and its elements are in the same order, except for
     *  the insertion of the given element.
     *  @param s2 the shorter sequence, which we see if the elem is
     *            inserted into
     *  @param elem the given element
     *  @return whether the elements of s2 occur in order in this
     *          sequence, with the insertion of elem somewhere.
     * @see #isDeletionFrom
     * @see #isProperSupersequence
     * @see #isProperSubsequence
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < int_length();
      @                         itemAt(i) .equals(elem)
      @                         && subsequence(0,i)
      @                            .concat(subsequence((int)(i+1),int_length()))
      @                            .equals(s2));
      @    ensures_redundantly \result ==> this.int_length() == s2.int_length()+1;
      @    ensures_redundantly \result ==> has(elem);
      @    ensures_redundantly \result <==> s2.isDeletionFrom(this, elem);
      @*/
    public boolean isInsertionInto(/*@ non_null @*/ JMLEqualsSequence s2,
                                   Object elem) {
        if (int_length() != s2.int_length() + 1) {
            return false;
        }
        JMLListEqualsNode walker = theSeq;
        JMLListEqualsNode s2walker = s2.theSeq;
        /*@ maintaining subsequence(0, (int)(int_length()-lenRemaining))
          @                 .equals(s2.subsequence(0, (int)(int_length()-lenRemaining)));
          @ decreasing int_length();
          @*/
        for (int lenRemaining = int_length(); lenRemaining > 0; lenRemaining--) {
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

    /** Tells whether this sequence is the result of deleting the
     *  given element once from the given sequence.  That is, this
     *  sequence is exactly one element shorter than the given
     *  sequence, and its elements are in the same order, except for
     *  the deletion of the given element from the given sequence.
     *  @param s2 the longer sequence, in which we see if the elem is
     *            deleted from
     *  @param elem the given element
     *  @return whether the elements of s2 occur in order in this
     *          sequence, with the deletion of elem somewhere.
     * @see #isInsertionInto
     * @see #isProperSupersequence
     * @see #isProperSubsequence
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < s2.int_length();
      @                         s2.itemAt(i) .equals(elem)
      @                         && this.equals(s2.removeItemAt(i)));
      @    ensures_redundantly \result ==> this.int_length()+1 == s2.int_length();
      @    ensures_redundantly \result ==> s2.has(elem);
      @    ensures_redundantly \result <==> s2.isInsertionInto(this, elem);
      @*/
    public boolean isDeletionFrom(/*@ non_null @*/ JMLEqualsSequence s2,
                                  Object elem) {
        return s2.isInsertionInto(this, elem);
    }  

    // *************** building new JMLEqualsSequences **********************

    /** Return a clone of this object.  This method does not clone the
     * elements of the sequence.
     */
    /*@ also
      @  public normal_behavior
      @   ensures \result != null
      @        && \result instanceof JMLEqualsSequence
      @        && ((JMLEqualsSequence)\result).equals(this);
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
      @                    ==> \result.itemAt(i) .equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @
      @
      @ model public JMLEqualsSequence prefix(\bigint n);
      @*/

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
      @            && (\forall int i; 0 <= i && i < n;
      @                   (\result.itemAt(i) != null 
      @                    ==> \result.itemAt(i) .equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @ also
      @  public behavior
      @    ensures !containsNull ==> !\result.containsNull;
      @
      @*/
      public /*@ non_null @*/ JMLEqualsSequence prefix(int n)
	  throws JMLSequenceException {
	  if (n < 0 || n > int_length()) {
	      throw new
		  JMLSequenceException("Invalid parameter to prefix() with n = " 
				       + n + "\n"
				       + "   when sequence length = " + int_length());
	  } else {
	      if (n == 0) {
		  return new JMLEqualsSequence();
	      } else {
		  JMLListEqualsNode pfx_list = theSeq.prefix(n);
		  return new JMLEqualsSequence(pfx_list, n);
	      }
	  }
      }  

    /** Return a sequence containing all but the first n elements in this.
     *  @param n the number of elements to remove
     *  @exception JMLSequenceException if n is negative or greater than
     *  the length of the sequence.
     * @see #header
     * @see #prefix
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt(i-n) != null 
      @                   && \result.itemAt(i-n) .equals(itemAt(i)))
      @               || (\result.itemAt(i-n) == null 
      @                   && itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @
      model public JMLEqualsSequence removePrefix(\bigint n);
      @*/  

    /** Return a sequence containing all but the first n elements in this.
     *  @param n the number of elements to remove
     *  @exception JMLSequenceException if n is negative or greater than
     *  the length of the sequence.
     * @see #header
     * @see #prefix
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt((int)(i-n)) != null 
      @                   && \result.itemAt((int)(i-n)) .equals(itemAt(i)))
      @               || (\result.itemAt((int)(i-n)) == null 
      @                   && itemAt(i) == null) );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ JMLEqualsSequence removePrefix(int n)
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
                JMLListEqualsNode pfx_list = theSeq.removePrefix(n);
                return new JMLEqualsSequence(pfx_list, int_length()-n);
            }
        }
    }  

    /** Return a sequence that is the concatenation of this with
     *  the given sequence.
     *  @param s2 the sequence to place at the end of this sequence in
     *  the result.
     *  @return the concatenation of this sequence and s2.
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result.int_length() == int_length() + s2.int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                   (\result.itemAt(i) != null 
      @                    && \result.itemAt(i) .equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    && itemAt(i) == null) )
      @         && (\forall int i; 0 <= i && i < s2.int_length();
      @                   (\result.itemAt((int)(int_length()+i)) != null 
      @                    && \result.itemAt((int)(int_length()+i)) .equals(s2.itemAt(i)))
      @                || (\result.itemAt((int)(int_length()+i)) == null 
      @                    && s2.itemAt(i) == null) );
      @*/
    public /*@ non_null @*/
        JMLEqualsSequence concat(/*@ non_null @*/ JMLEqualsSequence s2) {
        if (theSeq == null) {
            return s2;
        } else if (s2.theSeq == null) {
            return this;
        } else {
            JMLListEqualsNode new_list = theSeq.concat(s2.theSeq);
            return new JMLEqualsSequence(new_list,
                                         int_length() + s2.int_length());
        }
    } 

    /** Return a sequence that is the reverse of this sequence.
     *  @return the reverse of this sequence.
     */
    /*@  public normal_behavior
      @    old int len = int_length();
      @    ensures \result.int_length() == len
      @         && (\forall int i; 0 <= i && i < len;
      @                   (\result.itemAt((int)(len-i-1)) != null 
      @                    && \result.itemAt((int)(len-i-1)) .equals(itemAt(i)))
      @                || (\result.itemAt((int)(len-i-1)) == null 
      @                    && itemAt(i) == null) );
      @ also
      @ public behavior
      @    ensures elementType == \result.elementType;
      @    ensures containsNull <==> \result.containsNull;
      @*/
    public /*@ non_null @*/ JMLEqualsSequence reverse() {
        if (theSeq == null) {
            return this;
        } else {
            JMLListEqualsNode r = theSeq.reverse();
            return new JMLEqualsSequence(r, int_length());
        }
    } 

    /** Return a sequence like this, but without the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #removeItemAt
     * @see #prefix
     * @see #removePrefix
     * @see #subsequence
     * @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < length();
      @    ensures \result.equals(prefix(index).concat(removePrefix(index+1)));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals (JMLSequenceException);
      @
      @
      model public  non_null  JMLEqualsSequence removeItemAt(\bigint index)
      throws JMLSequenceException;
      @*/
    
    /** Return a sequence like this, but without the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #removeItemAt
     * @see #prefix
     * @see #removePrefix
     * @see #subsequence
     * @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < int_length();
      @    ensures \result.equals(prefix(index).concat(removePrefix((int)(index+1))));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < int_length());
      @    signals (JMLSequenceException);
      @
      @*/
    public /*@ non_null @*/ JMLEqualsSequence removeItemAt(int index)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            JMLListEqualsNode new_list = theSeq.removeItemAt(index);
            return new JMLEqualsSequence(new_list, int_length()-1);
        } else {
            throw new
                JMLSequenceException("Invalid parameter to removeItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + int_length());
        }
    }

    /** Return a sequence like this, but with item replacing the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @param item the item to put at index index
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #replaceItemAt
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < length();
      @    ensures \result.equals(removeItemAt(index).insertBeforeIndex(index,
      @                                                                 item));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals (JMLSequenceException);
      @
      model public  non_null  JMLEqualsSequence
      replaceItemAt(\bigint index, Object item)
      throws JMLSequenceException;
      @*/

    /** Return a sequence like this, but with item replacing the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @param item the item to put at index index
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #replaceItemAt
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < int_length();
      @    ensures \result.equals(removeItemAt(index).insertBeforeIndex(index,
      @                                                                 item));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < int_length());
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ JMLEqualsSequence
        replaceItemAt(int index, Object item)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            // replaceItemAt() clones item, if necessary
            JMLListEqualsNode new_list = theSeq.replaceItemAt(index, item);
            return new JMLEqualsSequence(new_list, int_length());
        } else {
            throw new
                JMLSequenceException("Invalid parameter to replaceItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + int_length());
        }
    } 

    /** Return a sequence containing all but the last element in this.
     *  @exception JMLSequenceException if this is empty.
     *  @see #prefix
     *  @see #first
     *  @see #last
     *  @see #trailer
     *  @see #subsequence
     */
    /*@  public normal_behavior
      @    requires int_length() >= 1;
      @    ensures \result.equals(removeItemAt((int)(int_length()-1)));
      @    ensures_redundantly \result.int_length() == int_length() - 1;
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @
      @*/
    public /*@ non_null @*/ JMLEqualsSequence header()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried header() on empty sequence.");
        } else {
            JMLListEqualsNode new_list = theSeq.removeLast();
            return new JMLEqualsSequence(new_list, int_length() - 1);
        }   
    }

    /** Return a sequence containing all but the first element in this.
     *  @exception JMLSequenceException if this is empty.
     *  @see #removePrefix
     *  @see #last
     *  @see #first
     *  @see #header
     *  @see #subsequence
     */
    /*@  public normal_behavior
      @    requires int_length() >= 1;
      @    ensures \result.equals(removePrefix(1));
      @    ensures_redundantly \result.int_length() == int_length() - 1;
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @*/
    public /*@ pure @*/ /*@ non_null @*/ JMLEqualsSequence trailer()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried trailer() on empty sequence.");
        } else {
            JMLListEqualsNode new_list = theSeq.next;
            return new JMLEqualsSequence(new_list, int_length() - 1);
        }   
    }  


    /** Return a sequence like this, but with item put immediately after
     *  the given index.
     *  @param afterThisOne a zero-based index into the sequence, or -1.
     *  @param item the item to put after index afterThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertBeforeIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
    /*@ //FIXME, _ alsoIfValue _
      @  public normal_behavior
      @    requires -1 <= afterThisOne && afterThisOne < length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex((int)(afterThisOne + 1), item));
      @ also
      @  public exceptional_behavior
      @    requires !(-1 <= afterThisOne && afterThisOne < length);
      @    signals (JMLSequenceException);
      @
      model public JMLEqualsSequence insertAfterIndex(\bigint afterThisOne,
      Object item)  
      throws JMLSequenceException, IllegalStateException;
      @*/


    /** Return a sequence like this, but with item put immediately after
     *  the given index.
     *  @param afterThisOne a zero-based index into the sequence, or -1.
     *  @param item the item to put after index afterThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertBeforeIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
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
    public /*@ non_null @*/ JMLEqualsSequence insertAfterIndex(int afterThisOne,
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

    /** Return a sequence like this, but with item put immediately
     *  before the given index.
     *  @param beforeThisOne a zero-based index into the sequence,
     *         or the length of this.
     *  @param item the item to put before index beforeThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertAfterIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
    /*@ //FIXME, _ alsoIfValue _
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLEqualsSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      @
      model public  
        JMLEqualsSequence insertBeforeIndex(\bigint beforeThisOne, Object item)
        throws JMLSequenceException, IllegalStateException ;
    @*/

    /** Return a sequence like this, but with item put immediately
     *  before the given index.
     *  @param beforeThisOne a zero-based index into the sequence,
     *         or the length of this.
     *  @param item the item to put before index beforeThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertAfterIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
    /*@ 
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLEqualsSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ 
        JMLEqualsSequence insertBeforeIndex(int beforeThisOne, Object item)
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
                return new JMLEqualsSequence(item);
            } else {
                // insertBefore() clones item, if necessary
                JMLListEqualsNode new_list
                    = theSeq.insertBefore(beforeThisOne, item);
                return new JMLEqualsSequence(new_list, int_length()+1);
            }
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    } 

    /** Return a sequence like this, but with the given item put an the end.
     *  @param item the item to put at the end of the result.
     *  @return a sequence the elements of this sequence followed by item.
     *  @see #insertAfterIndex
     *  @see #insertBeforeIndex
     *  @see #insertFront
     *  @see #removeItemAt
     *  @see #header
     *  @see #last
     */
    /*@ 
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(int_length(), item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && isProperPrefix(\result);
      @*/
    public /*@ non_null @*/ JMLEqualsSequence insertBack(Object item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLEqualsSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            // append() clones item, if necessary
            return new JMLEqualsSequence(theSeq.append(item), int_length()+1);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }

    /** Return a sequence like this, but with the given item put an the front.
     *  @param item the item to put at the front of the result.
     *  @return a sequence with item followed by the elements of this sequence.
     *  @see #insertAfterIndex
     *  @see #insertBeforeIndex
     *  @see #insertBack
     *  @see #removeItemAt
     *  @see #trailer
     *  @see #first
     */
    /*@ 
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(0, item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && \result.trailer().equals(this);
      @*/
    public /*@ pure @*/ /*@ non_null @*/ JMLEqualsSequence insertFront(Object item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLEqualsSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            return new JMLEqualsSequence(  // cons() clones item, if necessary
                                         JMLListEqualsNode.cons(item, theSeq),
                                         int_length()+1);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }

    /** Returns a subsequence of this containing the elements beginning
     *   with index from (inclusive) and ending with index to (exclusive).
     *  @param from the inclusive, zero-based element of the first
     *  element in the subsequence.
     *  @param to the zero-based element of the first element that
     *  should not be in the subsequence.
     *  @exception JMLSequenceException if (from < 0 or from > to
     *  or to > length of this.
     *  @see #prefix
     *  @see #removePrefix
     *  @see #header
     *  @see #trailer
     *  @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= from && from <= to && to <= length();
      @    ensures \result.equals(removePrefix(from).prefix((int)(to - from)))
      @         && \result.length() == to - from;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= from && from <= to && to <= length());
      @    signals (JMLSequenceException);
      @ also
      @ public behavior
      @    ensures !\result.containsNull <== !containsNull;
      @
    model public  non_null  JMLEqualsSequence subsequence(\bigint from, \bigint to)
        throws JMLSequenceException ;
	@*/

    /** Returns a subsequence of this containing the elements beginning
     *   with index from (inclusive) and ending with index to (exclusive).
     *  @param from the inclusive, zero-based element of the first
     *  element in the subsequence.
     *  @param to the zero-based element of the first element that
     *  should not be in the subsequence.
     *  @exception JMLSequenceException if (from < 0 or from > to
     *  or to > length of this.
     *  @see #prefix
     *  @see #removePrefix
     *  @see #header
     *  @see #trailer
     *  @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= from && from <= to && to <= int_length();
      @    ensures \result.equals(removePrefix(from).prefix((int)(to - from)))
      @         && \result.int_length() == to - from;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= from && from <= to && to <= int_length());
      @    signals (JMLSequenceException);
      @ also
      @ public behavior
      @    ensures !\result.containsNull <== !containsNull;
      @*/
    public /*@ non_null @*/ JMLEqualsSequence subsequence(int from, int to)
        throws JMLSequenceException {
        if (from < 0 || from > to || to > int_length()) {
            throw new JMLSequenceException("Invalid parameters to "
                                           + "subsequence() with from = " 
                                           + from + " and to = " + to + "\n"
                                           + "   " + "when sequence length = "
                                           + int_length());
        } else {
            if (theSeq == null) {
                return this;  // i.e., from == to == int_length() == 0
            } else {
                JMLListEqualsNode removedPrefix = theSeq.removePrefix(from);
                if (removedPrefix == null) {
                     return new JMLEqualsSequence();
                } else {
                    JMLListEqualsNode new_list = removedPrefix.prefix(to-from);
                     return new JMLEqualsSequence(new_list, to - from);
                }
            }
        }
    } 

    /** Return a new JMLEqualsBag containing all the elements of this.
     * @see #toSet()
     * @see #toArray()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall int i; 0 <= i && i < int_length();
      @                            \result.count(this.itemAt(i))
      @                             == this.count(this.itemAt(i)));
      @*/
    public /*@ non_null @*/ JMLEqualsBag toBag() {
        JMLEqualsBag ret = new JMLEqualsBag();
        JMLEqualsSequenceEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            Object e = (o == null ? null :  o);
            ret = ret.insert(e);
        }
        return ret;
    } 

    /** Return a new JMLEqualsSet containing all the elements of this.
     * @see #toBag()
     * @see #toArray()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall Object o;; \result.has(o) == this.has(o));
      @*/
    public /*@ non_null @*/ JMLEqualsSet toSet() {
        JMLEqualsSet ret = new JMLEqualsSet();
        JMLEqualsSequenceEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            Object e = (o == null ? null :  o);
            ret = ret.insert(e);
        }
        return ret;
    } 

    /** Return a new array containing all the elements of this in order.
     * @see #toSet()
     * @see #toBag()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                 (\result[i] == null ==> this.itemAt(i) == null)
      @              && (\result[i] != null ==>
      @                   \result[i] .equals(this.itemAt(i))));
      @*/
    public /*@ non_null @*/ Object[] toArray() {
        Object[] ret = new Object[int_length()];
        JMLEqualsSequenceEnumerator enum = elements();
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

    //********************** Tools Methods *********************************

    // The enumerator method and toString are of no value for writing
    // assertions in JML. They are included for the use of developers
    // of CASE tools based on JML, e.g., type checkers, assertion
    // evaluators, prototype generators, test tools, ... . They can
    // also be used in model programs in specifications.

    /** Return a enumerator for this.
     * @see #iterator()
     * @see #itemAt()
     */
    /*@  public normal_behavior
      @    ensures \fresh(\result);
      @*/
    public /*@ non_null @*/ JMLEqualsSequenceEnumerator elements() {
        JMLEqualsSequenceEnumerator retValue 
            = new JMLEqualsSequenceEnumerator(this);
        return retValue;
    }  

    /** Returns an iterator over this sequence.
     * @see #elements()
     */
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
        JMLListEqualsNode seqWalker = theSeq;
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
