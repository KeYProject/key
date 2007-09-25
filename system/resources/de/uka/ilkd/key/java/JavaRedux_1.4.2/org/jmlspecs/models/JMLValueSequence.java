// @(#)$Id: JMLValueSequence.java 1.2 Fri, 06 May 2005 15:27:39 +0200 engelc $

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

public /*@ pure @*/ class JMLValueSequence
    extends JMLValueSequenceSpecs implements JMLCollection
{


    /*@ public invariant (\forall JMLValueSequence s2;
      @                    (\forall JMLType e1, e2;
      @                     (\forall \bigint n;
      @                       equational_theory(this, s2, e1, e2, n) )));
      @*/

    /*@ public normal_behavior
      @ {|
      @  // The following are defined by observations (itemAt) and induction.
      @ 
      @    ensures \result <==> !(new JMLValueSequence()).has(e1);
      @  also
      @    ensures \result <==> (new JMLValueSequence()).size() == 0;
      @  also
      @    ensures \result <==> (new JMLValueSequence(e1)).size() == 1;
      @  also
      @    ensures \result <==> 
      @        e1 != null ==>
      @        (new JMLValueSequence(e1)).itemAt(0).equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).first().equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).last().equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).itemAt(0).equals(e1);
      @  also
      @    ensures \result <==>
      @        s.insertFront(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).itemAt(s.size()).equals(e1);
      @  also
      @    ensures \result <==>
      @        s.insertBack(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==> 
      @        -1 <= n && n < s.size() && e1 != null
      @          ==> s.insertAfterIndex(n, e1).itemAt(n+1).equals(e1);
      @  also
      @    ensures \result <==> 
      @        -1 <= n && n < s.size()
      @          ==> s.insertAfterIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        0 <= n && n <= s.size() && e1 != null
      @          ==> s.insertBeforeIndex(n, e1).itemAt(n).equals(e1);
      @  also
      @    ensures \result <==> 
      @        0 <= n && n <= s.size()
      @          ==> s.insertBeforeIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        s.isPrefix(s2)
      @           == (\forall int i; 0 <= i && i < s.int_length();
      @                  (s2.itemAt(i) != null 
      @                   && s2.itemAt(i).equals(s.itemAt(i)))
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
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertFront(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertBack(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertAfterIndex(-1, e1));
      @ also
      @   ensures \result <==>
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertBeforeIndex(0, e1));
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
      @ // other ways to specify some operations
      public pure model boolean equational_theory(JMLValueSequence s,
                                                  JMLValueSequence s2,
                                                  JMLType e1,
                                                  JMLType e2, \bigint n);
      @*/

    /*@ public normal_behavior
      @  requires true;
      @ public static model pure BigInteger bigintToBigInteger(\bigint biValue);      @*/

    /*@ public normal_behavior
      @  requires oBi.equals(BigInteger.ZERO);
      @  ensures \result == (\bigint)0;
      @ public static model pure \bigint bigIntegerToBigint(BigInteger oBi);
      @*/


    //@ public invariant elementType <: \type(JMLType);
    /*@ public invariant
      @           (\forall JMLType o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    //@ public invariant_redundantly isEmpty() ==> !containsNull;

    /** The list representing this sequence's elements, in order.
     */
    protected final JMLListValueNode theSeq;
    //@                                 in objectState;
    //@ invariant theSeq != null ==> theSeq.owner == this;

    /** This sequence's length.
     */
    protected final BigInteger _length;
    //@                    in objectState;
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
    public JMLValueSequence() {
        theSeq = null;
        _length = BigInteger.ZERO;
    }  

    /*@  public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures int_length() == 1;
      @    ensures (e == null ==> itemAt(0) == null)
      @         && (e != null ==> itemAt(0).equals(e)); 
      @*/
    public JMLValueSequence (JMLType e)
    {
        theSeq = JMLListValueNode.cons(e, null); // cons() clones e, if needed
        _length = BigInteger.ONE;
    }

    /*@  public normal_behavior  
      @    requires ls == null <==> len == 0;
      @    requires len >= 0;
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures ls != null ==> elementType == ls.elementType;
      @    ensures ls != null ==> containsNull == ls.containsNull;
      @    ensures ls == null ==> elementType <: \type(JMLType);
      @    ensures ls == null ==> !containsNull;
      model protected JMLValueSequence (JMLListValueNode ls, \bigint len);
      @*/

    /*@    requires ls == null <==> len == 0;
      @    requires len >= 0;
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures ls != null ==> elementType == ls.elementType;
      @    ensures ls != null ==> containsNull == ls.containsNull;
      @    ensures ls == null ==> elementType <: \type(JMLType);
      @    ensures ls == null ==> !containsNull;
      @*/
    protected JMLValueSequence (JMLListValueNode ls, int len){
        theSeq = ls;	
        _length = BigInteger.valueOf(len);
    }


    public static final /*@ non_null @*/ JMLValueSequence EMPTY
        = new JMLValueSequence();

    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result != null && \result.equals(new JMLValueSequence(e));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence singleton(JMLType e)
    {
        return new JMLValueSequence(e);
    }

    /*@ public normal_behavior
      @    requires a != null;
      @    assignable \nothing;
      @    ensures \result != null && \result.size() == a.length
      @         && (\forall int i; 0 <= i && i < a.length;
      @                            (\result.itemAt(i) == null 
      @                               ? a[i] == null
      @                               : \result.itemAt(i).equals(a[i])));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/JMLType[] a)
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        for (int i = a.length-1; 0 <= i; i--) {
            ret = ret.insertFront(a[i]);
        }
        return ret;
    } 

    /*@ public normal_behavior
      @    requires a != null && 0 <= size && size < a.length;
      @    assignable \nothing;
      @    ensures \result != null && \result.size() == size
      @         && (\forall int i; 0 <= i && i < size;
      @                            (\result.itemAt(i) == null 
      @                               ? a[i] == null
      @                               : \result.itemAt(i).equals(a[i])));
      @
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/JMLType[] a, int size)
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        for (int i = size-1; 0 <= i; i--) {
            ret = ret.insertFront(a[i]);
        }
        return ret;
    } 

    /*@   public normal_behavior
      @      requires c != null
      @           && c.elementType <: \type(JMLType);
      @      requires c.size() < Integer.MAX_VALUE;
      @      assignable \nothing;
      @      ensures \result != null && \result.size() == c.size()
      @           && (\forall JMLType x; c.contains(x) <==> \result.has(x))
      @           && (* the elements in \result are in the same order as c *);
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.contains(o);
      @                                  !(o instanceof JMLType));
      @      assignable \nothing;
      @      signals (ClassCastException);
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/ java.util.Collection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        java.util.Iterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insertBack(null);
            } else {
                ret = ret.insertBack((JMLType) o);
            }
        }
        return ret;
    } 


    /*@   public normal_behavior
      @      requires c != null
      @           && c.elementType <: \type(JMLType);
      @      requires c.size() < Integer.MAX_VALUE;
      @      assignable \nothing;
      @      ensures \result != null
      @           && (\forall JMLType x; c.has(x) <==> \result.has(x))
      @           && (* the elements in \result are in the same order as c *);
      @      ensures_redundantly \result.size() == c.size();
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.has(o);
      @                                  !(o instanceof JMLType));
      @      assignable \nothing;
      @      signals (ClassCastException);
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/ JMLCollection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        JMLIterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insertBack(null);
            } else {
                ret = ret.insertBack((JMLType) o);
            }
        }
        return ret;
    }

    /*@ // _ alsoIfValue _ //FIXME! later
      @  public normal_behavior
      @    requires 0 <= i && i < length;
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length);
      @    signals (JMLSequenceException);
    model public JMLType itemAt(\bigint i) throws JMLSequenceException;
    @*/

    /*@ also
      @  public normal_behavior
      @    requires 0 <= i && i < int_size();
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < int_size());
      @    signals (JMLSequenceException);
      @*/
    public JMLType itemAt(int i) throws JMLSequenceException {
        if (i < 0 || i >= int_length()) {
            throw new JMLSequenceException("Index out of range.");
        } else {
            JMLListValueNode thisWalker = theSeq;
	      
            int k = 0;
            //@ loop_invariant 0 <= k && k <= i && thisWalker != null;
            for (; k < i; k++) {
                thisWalker = thisWalker.next;
            }   
            return (thisWalker.head());  
        }
    }    

    /*@  public normal_behavior
      @    requires 0 <= i && i < length; //FIXME, might use size();
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length); //FIXME, might use size());
      @    signals (IndexOutOfBoundsException);
      @
      model public JMLType get(\bigint i) throws IndexOutOfBoundsException ;
      @*/

    /*@  public normal_behavior
      @    requires 0 <= i && i < length;
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length);
      @    signals (IndexOutOfBoundsException);
      @
      @*/
    public JMLType get(int i) throws IndexOutOfBoundsException {
        try {
            JMLType ret = itemAt(i);
            return ret;
        } catch (JMLSequenceException e) {
            IndexOutOfBoundsException e2 = new IndexOutOfBoundsException();
            e2.initCause(e);
            throw e2;
        }
    }  

    /*@ public normal_behavior
      @   ensures \result == length;
      @ public model pure \bigint size();
      @*/


    /*@ public normal_behavior
      @   ensures \result == length;
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

    /*@ also
      @    public normal_behavior
      @      requires size() <= Integer.MAX_VALUE;
      @      ensures \result == size();
      @*/
    public int int_length( ) {
        return _length.intValue();
    }  

    /*@ //also //FIXME, remove // later
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of \bigint i; 0 <= i && i < length();
      @                             itemAt(i) != null
      @                             && itemAt(i).equals(item));
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of \bigint i; 0 <= i && i < length();
      @                                        itemAt(i) == null);
      model public \bigint bi_count(JMLType item);
      @*/

    /*@ also
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of int i; 0 <= i && i < int_length();
      @                             itemAt(i) != null
      @                             && itemAt(i).equals(item));
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of int i; 0 <= i && i < int_length();
      @                                        itemAt(i) == null);
      @*/
    public int count(JMLType item) {
        JMLListValueNode ptr = this.theSeq;
        int cnt = 0;
        //@ maintaining (* cnt is count of elements matching item so far *);
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
      @                                 itemAt(i).equals(elem));
      @      also
      @       requires elem == null;
      @        ensures \result <==> 
      @                  (\exists int i; 0 <= i && i < int_length(); 
      @                                  itemAt(i) == null);
      @    |}
      @*/
    public boolean has(JMLType elem) {
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
      @                    && s2.itemAt(i).equals(itemAt(i)))
      @                || (s2.itemAt(i) == null && itemAt(i) == null) );
      @*/
    public boolean isPrefix(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() <= s2.int_length()
            && (theSeq == null || theSeq.isPrefixOf(s2.theSeq));
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isPrefix(s2) && !this.equals(s2);
      @*/
    public boolean isProperPrefix(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() != s2.int_length() && isPrefix(s2);
    }  


    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @       int_length() <= s2.int_length()
      @       && this.equals(s2.removePrefix(s2.int_length() - int_length()));
      @*/
    public boolean isSuffix(/*@ non_null @*/ JMLValueSequence s2) {
        if (int_length() > s2.int_length()) {
            return false;
        } else if (int_length() == 0) {
            return true;
        } 
        JMLListValueNode suffix = s2.theSeq.removePrefix(s2.int_length() - int_length());
        return theSeq.equals(suffix);
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isSuffix(s2) && !this.equals(s2);
      @*/
    public boolean isProperSuffix(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() != s2.int_length() && isSuffix(s2);
    }  

    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLValueSequence;
      @     ensures \result <==>
      @          isPrefix((JMLValueSequence)obj)
      @          && ((JMLValueSequence)obj).isPrefix(this);
      @     ensures_redundantly \result ==>
      @          containsNull == ((JMLValueSequence)obj).containsNull;
      @ also
      @  public normal_behavior
      @    requires obj == null || !(obj instanceof JMLValueSequence);
      @    ensures !\result;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        return (obj != null && obj instanceof JMLValueSequence)
            && (int_length() == ((JMLValueSequence)obj).int_length())
            && isPrefix((JMLValueSequence)obj);
    }  

    public int hashCode() {
        return (theSeq == null ? 0 : theSeq.hashCode());
    }

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
      @       ensures itemAt(\result).equals(item)
      @             && (\forall \bigint i; 0 <= i && i < \result;
      @                                !(itemAt(i).equals(item)));
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
      model public \bigint bi_indexOf(JMLType item) throws JMLSequenceException;
      @*/

    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures itemAt(\result).equals(item)
      @             && (\forall int i; 0 <= i && i < \result;
      @                                !(itemAt(i).equals(item)));
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
    public int indexOf(JMLType item) throws JMLSequenceException {
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

    /*@ also
      @  public normal_behavior
      @    requires int_length() > 0;
      @    {|
      @       requires itemAt(0) != null;
      @       ensures \result.equals(itemAt(0));
      @      also
      @       requires itemAt(0) == null;
      @       ensures \result == null;
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @*/
    public /*@ pure @*/ JMLType first() throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried first() on empty sequence.");
        } else {
            return (theSeq.head()); 
        }   
    }

    /*@ also
      @  public normal_behavior
      @    requires int_length() >= 1;
      @    {|
      @       requires itemAt((int)(int_length()-1)) != null;
      @       ensures \result.equals(itemAt((int)(int_length()-1)));
      @     also
      @       requires itemAt((int)(int_length()-1)) == null;
      @       ensures \result == null;
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @*/
    public JMLType last() throws JMLSequenceException {
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
    public boolean isSubsequence(/*@ non_null @*/ JMLValueSequence s2) {
        JMLListValueNode walker = s2.theSeq;
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
    public boolean isProperSubsequence(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() < s2.int_length() && isSubsequence(s2);
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isSubsequence(this);
      @*/
    public boolean isSupersequence(/*@ non_null @*/ JMLValueSequence s2) {
        return s2.isSubsequence(this);
    }

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isProperSubsequence(this);
      @*/
    public
        boolean isProperSupersequence(/*@ non_null @*/ JMLValueSequence s2) {
        return s2.isProperSubsequence(this);
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < int_length();
      @                         itemAt(i).equals(elem)
      @                         && subsequence(0,i)
      @                            .concat(subsequence((int)(i+1),int_length()))
      @                            .equals(s2));
      @    ensures_redundantly \result ==> this.int_length() == s2.int_length()+1;
      @    ensures_redundantly \result ==> has(elem);
      @    ensures_redundantly \result <==> s2.isDeletionFrom(this, elem);
      @*/
    public boolean isInsertionInto(/*@ non_null @*/ JMLValueSequence s2,
                                   JMLType elem) {
        if (int_length() != s2.int_length() + 1) {
            return false;
        }
        JMLListValueNode walker = theSeq;
        JMLListValueNode s2walker = s2.theSeq;
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

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < s2.int_length();
      @                         s2.itemAt(i).equals(elem)
      @                         && this.equals(s2.removeItemAt(i)));
      @    ensures_redundantly \result ==> this.int_length()+1 == s2.int_length();
      @    ensures_redundantly \result ==> s2.has(elem);
      @    ensures_redundantly \result <==> s2.isInsertionInto(this, elem);
      @*/
    public boolean isDeletionFrom(/*@ non_null @*/ JMLValueSequence s2,
                                  JMLType elem) {
        return s2.isInsertionInto(this, elem);
    }  

    /*@ also
      @  public normal_behavior
      @   ensures \result != null
      @        && \result instanceof JMLValueSequence
      @        && ((JMLValueSequence)\result).equals(this);
      @*/
    public Object clone() { 
        if (theSeq == null) {
            return this;
        } else {
            return new JMLValueSequence((JMLListValueNode)theSeq.clone(),
                                        int_length());
        }
    }  

    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == n
      @            && (\forall \bigint i; 0 <= i && i < n;
      @                   (\result.itemAt(i) != null 
      @                    ==> \result.itemAt(i).equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the last length-n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @
      model public JMLValueSequence prefix(\bigint n) throws JMLSequenceException;
      @*/

    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == n
      @            && (\forall int i; 0 <= i && i < n;
      @                   (\result.itemAt(i) != null 
      @                    ==> \result.itemAt(i).equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the last length-n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @
      @*/
      public /*@ non_null @*/ JMLValueSequence prefix(int n)
	  throws JMLSequenceException {
	  if (n < 0 || n > int_length()) {
	      throw new
		  JMLSequenceException("Invalid parameter to prefix() with n = " 
				       + n + "\n"
				       + "   when sequence length = " + int_length());
	  } else {
	      if (n == 0) {
		  return new JMLValueSequence();
	      } else {
		  JMLListValueNode pfx_list = theSeq.prefix(n);
		  return new JMLValueSequence(pfx_list, n);
	      }
	  }
      }  

    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt(i-n) != null 
      @                   && \result.itemAt(i-n).equals(itemAt(i)))
      @               || (\result.itemAt(i-n) == null 
      @                   && itemAt(i) == null) );
      @    ensures_redundantly 
      @          (* \result is the same as this,
      @             but with the first n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @
    model public JMLValueSequence removePrefix(\bigint n) throws JMLSequenceException;
    @*/  


    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt((int)(i-n)) != null 
      @                   && \result.itemAt((int)(i-n)).equals(itemAt(i)))
      @               || (\result.itemAt((int)(i-n)) == null 
      @                   && itemAt(i) == null) );
      @    ensures_redundantly 
      @          (* \result is the same as this,
      @             but with the first n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/ JMLValueSequence removePrefix(int n)
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
                JMLListValueNode pfx_list = theSeq.removePrefix(n);
                return new JMLValueSequence(pfx_list, int_length()-n);
            }
        }
    }  

    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result.int_length() == int_length() + s2.int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                   (\result.itemAt(i) != null 
      @                    && \result.itemAt(i).equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    && itemAt(i) == null) )
      @         && (\forall int i; 0 <= i && i < s2.int_length();
      @                   (\result.itemAt((int)(int_length()+i)) != null 
      @                    && \result.itemAt((int)(int_length()+i)).equals(s2.itemAt(i)))
      @                || (\result.itemAt((int)(int_length()+i)) == null 
      @                    && s2.itemAt(i) == null) );
      @*/
    public /*@ non_null @*/
        JMLValueSequence concat(/*@ non_null @*/ JMLValueSequence s2) {
        if (theSeq == null) {
            return s2;
        } else if (s2.theSeq == null) {
            return this;
        } else {
            JMLListValueNode new_list = theSeq.concat(s2.theSeq);
            return new JMLValueSequence(new_list,
                                         int_length() + s2.int_length());
        }
    }

    /*@  public normal_behavior
      @    old int len = int_length();
      @    ensures \result.int_length() == len
      @         && (\forall int i; 0 <= i && i < len;
      @                   (\result.itemAt((int)(len-i-1)) != null 
      @                    && \result.itemAt((int)(len-i-1)).equals(itemAt(i)))
      @                || (\result.itemAt((int)(len-i-1)) == null 
      @                    && itemAt(i) == null) );
      @*/
    public /*@ non_null @*/ JMLValueSequence reverse() {
        if (theSeq == null) {
            return this;
        } else {
            JMLListValueNode r = theSeq.reverse();
            return new JMLValueSequence(r, int_length());
        }
    } 

    /*@  public normal_behavior
      @    requires 0 <= index && index < length();
      @    ensures \result.equals(prefix(index).concat(removePrefix(index+1)));
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the item at position index removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals (JMLSequenceException);
      @
    model public  non_null  JMLValueSequence removeItemAt(\bigint index) throws JMLSequenceException;
    @*/

    /*@  public normal_behavior
      @    requires 0 <= index && index < int_length();
      @    ensures \result.equals(prefix(index).concat(removePrefix((int)(index+1))));
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the item at position index removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < int_length());
      @    signals (JMLSequenceException);
      @
      @*/
    public /*@ non_null @*/ JMLValueSequence removeItemAt(int index)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            JMLListValueNode new_list = theSeq.removeItemAt(index);
            return new JMLValueSequence(new_list, int_length()-1);
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
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with item replacing the one at position index *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals (JMLSequenceException);
    model public  non_null  JMLValueSequence replaceItemAt(\bigint index, JMLType item) throws JMLSequenceException {
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
    public /*@ non_null @*/ JMLValueSequence
        replaceItemAt(int index, JMLType item)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            JMLListValueNode new_list = theSeq.replaceItemAt(index, item);
            return new JMLValueSequence(new_list, int_length());
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
    public /*@ non_null @*/ JMLValueSequence header()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried header() on empty sequence.");
        } else {
            JMLListValueNode new_list = theSeq.removeLast();
            return new JMLValueSequence(new_list, int_length() - 1);
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
    public /*@ pure @*/ /*@ non_null @*/ JMLValueSequence trailer()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried trailer() on empty sequence.");
        } else {
            JMLListValueNode new_list = theSeq.next;
            return new JMLValueSequence(new_list, int_length() - 1);
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
      model public JMLValueSequence insertAfterIndex(\bigint afterThisOne, JMLType item) throws JMLSequenceException, IllegalStateException;
      @*/


    /*@ also
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
      @*/
    public JMLValueSequence insertAfterIndex(int afterThisOne,
                                                             JMLType item)
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

    /*@ //FIXME, _ alsoIfValue _
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLValueSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      model public  
        JMLValueSequence insertBeforeIndex(\bigint beforeThisOne, JMLType item) throws JMLSequenceException, IllegalStateException;
    @*/

    /*@ also
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLValueSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      @*/
    public 
        JMLValueSequence insertBeforeIndex(int beforeThisOne, JMLType item)
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
                return new JMLValueSequence(item);
            } else {
                // insertBefore() clones item, if necessary
                JMLListValueNode new_list
                    = theSeq.insertBefore(beforeThisOne, item);
                return new JMLValueSequence(new_list, int_length()+1);
            }
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    } 

    /*@ also
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(int_length(), item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && isProperPrefix(\result);
      @    ensures_redundantly 
      @           (* \result is the same sequence as this,
      @              but with item.clone() inserted at the back,
      @              after index int_length() - 1 *);
      @*/
    public JMLValueSequence insertBack(JMLType item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLValueSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            return new JMLValueSequence(theSeq.append(item), int_length()+1);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }

    /*@ also
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(0, item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && \result.trailer().equals(this);
      @    ensures_redundantly 
      @          (* \result is the same sequence as this,
      @             but with item.clone() inserted at the front,
      @             before index 0 *);
      @*/
    public /*@ pure @*/ JMLValueSequence insertFront(JMLType item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLValueSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            return new JMLValueSequence(  // cons() clones item, if necessary
                                         JMLListValueNode.cons(item, theSeq),
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
    model public  non_null  JMLValueSequence subsequence(\bigint from, \bigint to) throws JMLSequenceException;
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
    public /*@ non_null @*/ JMLValueSequence subsequence(int from, int to)
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
                JMLListValueNode removedPrefix = theSeq.removePrefix(from);
                if (removedPrefix == null) {
                    return new JMLValueSequence();
                } else {
                    JMLListValueNode new_list = removedPrefix.prefix(to-from);
                    return new JMLValueSequence(new_list, to - from);
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
    public /*@ non_null @*/ JMLValueBag toBag() {
        JMLValueBag ret = new JMLValueBag();
        JMLValueSequenceEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            JMLType e = (o == null ? null : (JMLType)  o);
            ret = ret.insert(e);
        }
        return ret;
    } 

    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall JMLType o;; \result.has(o) == this.has(o));
      @*/
    public /*@ non_null @*/ JMLValueSet toSet() {
        JMLValueSet ret = new JMLValueSet();
        JMLValueSequenceEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            JMLType e = (o == null ? null : (JMLType)  o);
            ret = ret.insert(e);
        }
        return ret;
    } 

    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                 (\result[i] == null ==> this.itemAt(i) == null)
      @              && (\result[i] != null ==>
      @                   \result[i].equals(this.itemAt(i))));
      @*/
    public /*@ non_null @*/ JMLType[] toArray() {
        JMLType[] ret = new JMLType[int_length()];
        JMLValueSequenceEnumerator enum = elements();
        int i = 0;
        //@ loop_invariant 0 <= i && i <= ret.length;
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            if (o == null) {
                ret[i] = null;
            } else {
                JMLType e = (JMLType)  o;
                ret[i] = (JMLType)  e.clone();
            }
            i++;
        }
        return ret;
    } 

    /*@  public normal_behavior
      @    ensures \fresh(\result) && (* \result is an enumerator for this *);
      @*/
    public /*@ non_null @*/ JMLValueSequenceEnumerator elements() {
        JMLValueSequenceEnumerator retValue 
            = new JMLValueSequenceEnumerator(this);
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

    /*@ also
      @  public normal_behavior
      @    ensures (* \result is a string representation of this *);
      @*/
    public String toString() {
        String newStr = "(<";
        JMLListValueNode seqWalker = theSeq;
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
