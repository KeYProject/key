// @(#)$Id: JMLObjectSet.java 1.3 Tue, 17 May 2005 14:57:40 +0200 engelc $

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

/** Sets of objects.  This type uses "==" to
 * compare elements, and does not clone elements that are passed into and
 * returned from the set's methods.
 *
 * <p>
 * For the purposes of informal specification in the methods below, we
 * assume there is a model field
 * <pre>public model mathematical_set theSet;</pre>
 * that you can think of as a mathematical set of objects.
 *
 * @version $Revision: 1.3 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLCollection
 * @see JMLType
 * @see JMLEqualsSet
 * @see JMLValueSet
 * @see JMLObjectSetEnumerator
 * 
 * @see JMLObjectBag
 * @see JMLEqualsBag
 * @see JMLValueBag
 */
//-@ immutable
public /*@ pure @*/ class JMLObjectSet
    implements JMLCollection
{

    //*********************** equational theory ***********************

    /*@ public invariant (\forall JMLObjectSet s2; s2 != null;
      @                    (\forall Object e1, e2; ;
      @                          equational_theory(this, s2, e1, e2) ));
      @*/

    /** An equational specification of the properties of sets.
     */
    /*@ public normal_behavior
      @ {|
      @     // The following are defined by using has and induction.
      @
      @       ensures \result <==> !(new JMLObjectSet()).has(e1);
      @     also
      @       ensures \result <==>
      @           s.insert(null).has(e2) == (e2 == null || s.has(e2));
      @     also
      @       ensures \result <==>
      @         (e1 != null
      @          ==> s.insert(e1).has(e2)
      @                == (e1 == e2 || s.has(e2)));
      @     also
      @       ensures \result <==>
      @           (new JMLObjectSet()).int_size() == 0;
      @     also
      @       ensures \result <==>
      @           s.insert(e1).int_size()
      @              == (s.has(e1) ? s.int_size() : s.int_size() + 1);
      @     also
      @       ensures \result <==>
      @           s.isSubset(s2)
      @              == (\forall Object o; ; s.has(o) ==> s2.has(o));
      @     also
      @       ensures \result <==>
      @           s.equals(s2) == (s.isSubset(s2) && s2.isSubset(s));
      @     also
      @       ensures \result <==>
      @           (new JMLObjectSet()).remove(e1).equals(new JMLObjectSet());
      @     also
      @       ensures \result <==>
      @           s.insert(null).remove(e2)
      @                     .equals
      @                     (e2 == null ? s : s.remove(e2).insert(null));
      @     also
      @       ensures \result <==>
      @           e1 != null
      @            ==> s.insert(e1).remove(e2)
      @                     .equals
      @                     (e1 == e2
      @                        ? s : s.remove(e2).insert(e1));
      @     also
      @       ensures \result <==>
      @         (s.union(s2)).has(e1) == (s.has(e1) || s2.has(e1));
      @     also
      @       ensures \result <==>
      @         (s.intersection(s2)).has(e1) == (s.has(e1) && s2.has(e1));
      @     also
      @       ensures \result <==>
      @         (s.difference(s2)).has(e1) == (s.has(e1) && !s2.has(e1));
      @
      @
      @     // The following are all defined as abbreviations.
      @
      @    also
      @      ensures \result <==>
      @         s.isEmpty() == (s.int_size() == 0);
      @    also
      @      ensures \result <==>
      @         (new JMLObjectSet(e1)).equals(new JMLObjectSet().insert(e1));
      @    also
      @      ensures \result <==>
      @         s.isProperSubset(s2)
      @               == ( s.isSubset(s2) && !s.equals(s2));
      @    also
      @      ensures \result <==>
      @         s.isSuperset(s2) == s2.isSubset(s);
      @    also
      @      ensures \result <==>
      @         s.isProperSuperset(s2) == s2.isProperSubset(s);
      @ |}
      @
      @ implies_that    // other ways to specify some operations
      @
      @      ensures \result <==> (new JMLObjectSet()).isEmpty();
      @ 
      @      ensures \result <==> !s.insert(e1).isEmpty();
      @
      @      ensures \result <==>
      @         (new JMLObjectSet(null)).has(e2) == (e2 == null);
      @
      @      ensures \result <==>
      @         (e1 != null
      @          ==> new JMLObjectSet(e1).has(e2)
      @              == (e1 == e2));
      @
      static public pure model boolean equational_theory(JMLObjectSet s,
                                                  JMLObjectSet s2,
                                                  Object e1,
                                                  Object e2);
      @*/
 
    //@ public  invariant elementType <: \type(Object);
    /*@ public invariant
      @           (\forall Object o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    //@ public invariant containsNull <==> has(null);
    //@ public invariant_redundantly isEmpty() ==> !containsNull;

    /** The list representing the elements of this set.
     */
    protected final JMLListObjectNode the_list;
    //@                                      in objectState;

    /** The number of elements in this set.
     */
    /*@ spec_public @*/ protected final int size;
    //@                                      in objectState;

    //@ protected invariant the_list == null ==> size == 0;
    //@ protected invariant the_list != null ==> size == the_list.int_size();
    //@ protected invariant (the_list == null) == (size == 0);
    //@ protected invariant size >= 0;
    /*@ protected invariant the_list != null && the_list.next != null ==>
      @       !the_list.next.has(the_list.val);
      @*/
    //@ protected invariant_redundantly (* the_list has no duplicates *);

    //@ protected invariant size == 0 ==> !containsNull;

    //@ public invariant owner == null;

    //************************* Constructors ********************************

    /** Initialize this to be an empty set.
     * @see #EMPTY
     */
    /*@ public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures this.isEmpty();
      @ implies_that
      @    ensures elementType <: \type(Object) && !containsNull;
      @*/
    public JMLObjectSet() {
        the_list = null;
        size = 0;
    }  

    /** Initialize this to be a singleton set containing the given element.
     * @see #singleton
     */
    public JMLObjectSet (Object e)
        /*@ public normal_behavior
          @    assignable objectState, elementType, containsNull, owner;
          @    ensures this.has(e) && this.int_size() == 1;
          @    ensures_redundantly
          @      (* this is a singleton set containing e *); 
          @*/
    {
        the_list = JMLListObjectNode.cons(e, null);  // cons() clones if needed
        size = 1;
    }  

    /** Initialize this set with the given instance variables.
     */
    //@    requires (ls == null) == (sz == 0);
    //@    requires sz >= 0;
    //@    assignable objectState, elementType, containsNull, owner;
    //@    ensures ls != null ==> elementType == ls.elementType;
    //@    ensures ls != null ==> containsNull == ls.containsNull;
    //@    ensures ls == null ==> elementType <: \type(Object);
    //@    ensures ls == null ==> !containsNull;
    protected JMLObjectSet (JMLListObjectNode ls, int sz) {
        the_list = ls;
        size = sz;
    }

    /** Initialize this set with the given list.
     */
    //@    assignable objectState, elementType, containsNull, owner;
    //@    ensures ls != null ==> elementType == ls.elementType;
    //@    ensures ls != null ==> containsNull == ls.containsNull;
    //@    ensures ls == null ==> elementType <: \type(Object);
    //@    ensures ls == null ==> !containsNull;
    protected JMLObjectSet (JMLListObjectNode ls) {
        this(ls, (ls == null) ? 0 : ls.int_size()); 
    }

    //**************************** Static methods ****************************

    /** The empty JMLObjectSet.
     * @see #JMLObjectSet()
     */
    public static final /*@ non_null @*/ JMLObjectSet EMPTY
        = new JMLObjectSet();

    /** Return the singleton set containing the given element.
     * @see #JMLObjectSet(Object)
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.equals(new JMLObjectSet(e));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet singleton(Object e)
    {
        return new JMLObjectSet(e);
    }

    /** Return the set containing all the elements in the given array.
     */
    /*@ public normal_behavior
      @    requires a != null;
      @    ensures \result != null && \result.int_size() == a.length
      @         && (\forall int i; 0 <= i && i < a.length; \result.has(a[i]));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet convertFrom(/*@ non_null @*/ Object[] a)
    {
        /*@ non_null @*/ JMLObjectSet ret = EMPTY;
        for (int i = 0; i < a.length; i++) {
            ret = ret.insert(a[i]);
        }
        return ret;
    } 

    /** Return the set containing all the object in the
     * given collection.
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     *  @see #containsAll(java.util.Collection)
     */
    /*@   public normal_behavior
      @      requires c != null
      @            && (\forall Object o; c.contains(o);
      @                                  o == null || (o instanceof Object));
      @      requires c.size() < Integer.MAX_VALUE;
      @      ensures \result != null && \result.int_size() == c.size()
      @           && (\forall Object x; c.contains(x) <==> \result.has(x));
      @  also
      @    public exceptional_behavior
      @      requires c != null
      @            && (\exists Object o; c.contains(o);
      @                              o != null && !(o instanceof Object));
      @      signals (ClassCastException);
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet convertFrom(/*@ non_null @*/ java.util.Collection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLObjectSet ret = EMPTY;
        java.util.Iterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insert(null);
            } else {
                ret = ret.insert(o);
            }
        }
        return ret;
    } 

    /** Return the set containing all the object in the
     * given JMLCollection.
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && (c.elementType <: \type(Object));
      @      ensures \result != null
      @           && (\forall Object x; c.has(x) <==> \result.has(x));
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.has(o);
      @                                  !(o instanceof Object));
      @      signals (ClassCastException);
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet convertFrom(/*@ non_null @*/ JMLCollection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLObjectSet ret = EMPTY;
        JMLIterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insert(null);
            } else {
                ret = ret.insert(o);
            }
        }
        return ret;
    }

    //**************************** Observers **********************************

    /** Is the argument "==" to one of the
     *  objects in theSet.
     */
    /*@ also
      @   public normal_behavior
      @     requires elem != null;
      @     ensures (* \result <==>
      @       elem is "==" to one of the objects in theSet *);
      @ also
      @   public normal_behavior
      @     requires elem == null;
      @     ensures (* \result <==> null is one of the objects in theSet *);
      @ also
      @   public normal_behavior
      @     requires isEmpty();
      @     ensures ! \result ;
      @*/    
    public /*@ pure @*/ boolean has(Object elem ) {
        return the_list != null && the_list.has(elem);
    }  

    /** Tell whether, for each element in the given collection, there is a
     * "==" element in this set.
     *  @param c the collection whose elements are sought.
     *  @see #isSuperset(JMLObjectSet)
     *  @see #convertFrom(java.util.Collection)
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

    /*@ also
      @   public normal_behavior
      @     ensures \result <==>
      @          s2 != null && s2 instanceof JMLObjectSet
      @          && (\forall Object e; ; this.has(e)
      @                                      == ((JMLObjectSet)s2).has(e));
      @     ensures_redundantly \result ==>
      @             s2 != null && s2 instanceof JMLObjectSet
      @             && containsNull == ((JMLObjectSet)s2).containsNull;
      @*/
    public boolean equals(Object s2) {
        return (s2 != null && s2 instanceof JMLObjectSet)
            && (size == ((JMLObjectSet)s2).int_size())
            && isSubset((JMLObjectSet)s2);
    }

    /** Return a hash code for this object.
     */
    public int hashCode() {
        if (size == 0) {
            return 0;
        } else {
            int hash = 0xffff;
            JMLListObjectNode walker = the_list;
            while (walker != null) {
                Object wv = walker.val;
                if (wv != null) {
                    hash ^= wv.hashCode();
                }
                walker = walker.next;
            }   
            return hash;
        }
    }

    /** Is the set empty.
     * @see #int_size()
     * @see #has(Object)
     */
    /*@   public normal_behavior
      @     ensures \result == (\forall Object e; ; !this.has(e));
      @ also
      @   protected normal_behavior
      @     ensures the_list == null <==> \result;
      @*/  
    public /*@ pure @*/ boolean isEmpty() {
        return the_list == null;
    }  

    /** Tells the number of elements in the set.
     */
    /*@ also
      @   public normal_behavior
      @    ensures 
      @       (this.isEmpty() ==> \result == 0)
      @       && (!this.isEmpty() ==>
      @             (\exists Object e; this.has(e);
      @                      \result == 1 + (this.remove(e).int_size())) );
      @ implies_that
      @    ensures \result >= 0;
      @*/
    public /*@ pure @*/ int int_size( ) {
        return size;
    }  

    /** Tells whether this set is a subset of or equal to the argument.
     * @see #isProperSubset(JMLObjectSet)
     * @see #isSuperset(JMLObjectSet)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @      (\forall Object e; ; this.has(e) ==> s2.has(e));
      @*/  
    public boolean isSubset(/*@ non_null @*/ JMLObjectSet s2) {
        if (size > s2.int_size()) {
            return false;
        } else {
            for (JMLListObjectNode walker = the_list;
                 walker != null;
                 walker = walker.next) {
                if (!s2.has(walker.val)) {
                    return false;
                }
            }   
            return true;
        }   
    }  

    /** Tells whether this set is a subset of but not equal to the
     * argument.
     * @see #isSubset(JMLObjectSet)
     * @see #isProperSuperset(JMLObjectSet)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @       this.isSubset(s2) && !this.equals(s2);
      @*/    
    public boolean isProperSubset(/*@ non_null @*/ JMLObjectSet s2) {
        return size < s2.int_size() && isSubset(s2);
    }  

    /** Tells whether this set is a superset of or equal to the argument.
     * @see #isProperSuperset(JMLObjectSet)
     * @see #isSubset(JMLObjectSet)
     * @see #containsAll(java.util.Collection)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result == s2.isSubset(this);
      @*/    
    public boolean isSuperset(/*@ non_null @*/ JMLObjectSet s2) {
        return s2.isSubset(this);
    }

    /** Tells whether this set is a superset of but not equal to the
     * argument.
     * @see #isSuperset(JMLObjectSet)
     * @see #isProperSubset(JMLObjectSet)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result == s2.isProperSubset(this);
      @*/
    public boolean isProperSuperset(/*@ non_null @*/ JMLObjectSet s2) {
        return s2.isProperSubset(this);
    }  

    /** Return an arbitrary element of this.
     *  @exception JMLNoSuchElementException if this is empty.
     *  @see #isEmpty()
     *  @see #elements()
     */
    /*@   public normal_behavior
      @      requires !isEmpty();
      @      ensures (\exists Object e; this.has(e);
      @                   (\result == null ==> e == null)
      @                && (\result != null ==> \result == e));
      @ also
      @   public exceptional_behavior
      @     requires isEmpty();
      @     signals (JMLNoSuchElementException);
      @ implies_that
      @   protected behavior
      @      ensures \result != null ==> \typeof(\result) <: elementType;
      @      ensures !containsNull ==> \result != null;
      @      signals (JMLNoSuchElementException) the_list == null;
      @*/
    public Object choose() throws JMLNoSuchElementException {
        if (the_list != null) {
            Object entry = the_list.val;
            if (entry == null) {
                return null;
            } else {
                Object o = entry ;
                return (Object) o;
            }
        } else {
            throw new JMLNoSuchElementException("Tried to .choose() "
                                                + "with JMLObjectSet empty");
        }
    }  

    // ****************** building new JMLObjectSets **************************

    /** Return a clone of this object.  This method does not clone the
     * elements of the set.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null
      @          && \result instanceof JMLObjectSet
      @          && this.equals(\result);
      @*/
    public Object clone() { 
        return this;
    }

    /** Returns a new set that contains all the elements of this and
     *  also the given argument.
     *  @see #has(Object)
     *  @see #remove(Object)
     */
    /*@ 
      @  public normal_behavior
      @   requires int_size() < Integer.MAX_VALUE || has(elem);
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @        \result.has(e) <==> this.has(e)
      @                            || (e == null && elem == null)
      @                            || (e != null && e == elem));
      @   ensures_redundantly this.isSubset(\result) && \result.has(elem)
      @     && \result.int_size() == this.int_size() + (this.has(elem) ? 0 : 1);
      @ also public normal_behavior
      @   ensures elem == null ==> \result.containsNull;
      @   ensures elem != null ==> \result.containsNull == containsNull;
      @*/  
    public /*@ non_null @*/ JMLObjectSet insert(Object elem)
        throws IllegalStateException
    {
        if (has(elem)) {
            return this;
        } else if (size < Integer.MAX_VALUE) {
            return fast_insert(elem);            
        } else {
            throw new IllegalStateException("Cannot insert into a set "
                                            +"with Integer.MAX_VALUE elements");
        }
    } 

    /** Returns a new set that contains all the elements of this and
     *  also the given argument, assuming the argument is not in the set.
     *  @see #insert(Object)
     */
    /*@ protected normal_behavior
      @   requires !has(elem);
      @   requires int_size() < Integer.MAX_VALUE;
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @        \result.has(e) <==> this.has(e)
      @                            || (e == null && elem == null)
      @                            || (e != null && e == elem));
      @   ensures_redundantly this.isSubset(\result) && \result.has(elem)
      @     && \result.int_size() == this.int_size() + 1;
      @*/  
    protected /*@ non_null @*/ JMLObjectSet fast_insert(Object elem) {
        return new JMLObjectSet(  // cons() clones if necessary
                                JMLListObjectNode.cons(elem, the_list),
                                size+1);
    }

    /** Returns a new set that contains all the elements of this except for
     *  the given argument.
     *  @see #has(Object)
     *  @see #insert(Object)
     */
    /*@ public normal_behavior
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @       \result.has(e) <==>
      @          this.has(e) && !((e == null && elem == null)
      @                           || (e != null && e == elem)));
      @   ensures_redundantly \result.isSubset(this) && !\result.has(elem)
      @      && \result.int_size() == this.int_size() - (this.has(elem) ? 1 : 0);
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/ JMLObjectSet remove(Object elem) {
        if (!has(elem)) {
            return this;
        } else {
            JMLListObjectNode new_list = the_list.remove(elem);
            return new JMLObjectSet(new_list, size - 1);
        }
    } 

    /** Returns a new set that contains all the elements that are in
     *  both this and the given argument.
     *  @see #union(JMLObjectSet)
     *  @see #difference(JMLObjectSet)
     */
    /*@ public normal_behavior
      @   requires s2 != null;
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @            \result.has(e) <==> this.has(e) && s2.has(e));
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull || !s2.containsNull
      @             ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/
        JMLObjectSet intersection(/*@ non_null @*/ JMLObjectSet s2) {
        JMLObjectSet returnSet = new JMLObjectSet();
        JMLListObjectNode thisWalker = the_list;
        while (thisWalker != null) {
            if (s2.has(thisWalker.val)) {
                returnSet = returnSet.fast_insert(thisWalker.val);
            }
            thisWalker = thisWalker.next;
        }   
        return returnSet;
    } 

    /** Returns a new set that contains all the elements that are in
     *  either this or the given argument.
     *  @see #intersection(JMLObjectSet)
     *  @see #difference(JMLObjectSet)
     */
    /*@ public normal_behavior
      @   requires s2 != null;
      @   requires int_size() < Integer.MAX_VALUE - s2.difference(this).int_size();
      @   ensures \result != null
      @	       && (\forall Object e; ;
      @               \result.has(e) <==> this.has(e) || s2.has(e));
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull && !s2.containsNull
      @             ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/
        JMLObjectSet union(/*@ non_null @*/ JMLObjectSet s2)
        throws IllegalStateException
    {
        JMLObjectSet returnSet = s2;
        JMLListObjectNode thisWalker = the_list;
        while (thisWalker != null) {
            returnSet = returnSet.insert(thisWalker.val);
            thisWalker = thisWalker.next;
        }
        return returnSet;
    } 

    /** Returns a new set that contains all the elements that are in
     *  this but not in the given argument.
     *  @see #union(JMLObjectSet)
     *  @see #difference(JMLObjectSet)
     */
    /*@ public normal_behavior
      @   requires s2 != null;
      @   ensures \result != null
      @	       && (\forall Object e; ;
      @                 \result.has(e) <==> this.has(e) && !s2.has(e));
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/
        JMLObjectSet difference(/*@ non_null @*/ JMLObjectSet s2) {
        JMLObjectSet returnSet = new JMLObjectSet();
        JMLListObjectNode thisWalker = the_list;
        while (thisWalker != null) {
            if (!s2.has(thisWalker.val)) {
                returnSet = returnSet.fast_insert(thisWalker.val);
            }
            thisWalker = thisWalker.next;
        }   
        return returnSet;
    } 

    /** Returns a new set that is the set of all subsets of this.
     */
    /*@ public normal_behavior
      @   requires int_size() < 32;
      @   ensures \result != null
      @	    && (\forall JMLObjectSet s; ;
      @               s.isSubset(this) <==> \result.has(s));
      @   ensures_redundantly \result != null
      @              && (0 < size && size <= 31
      @                  ==> \result.int_size() == (2 << (int_size()-1)));
      @*/
    public /*@ non_null @*/ JMLObjectSet powerSet()
        throws IllegalStateException
    {
        if (size >= 32) {
            throw new IllegalStateException("Can't compute the powerSet "
                                            + "of such a large set");
        }

        // This a dynamic programming algorithm.
        /*@ non_null @*/ JMLObjectSet ret = new JMLObjectSet(EMPTY);

        /*@ loop_invariant !ret.containsNull;
	  @ maintaining 0 <= i && i <= int_size() && ret.size >= 1
          @	  && (\forall JMLObjectSet s; s.int_size() <= i;
          @             s.isSubset(this) <==> ret.has(s));
          @  decreasing int_size()-i;
          @*/
        for (int i = 0; i < int_size(); i++) { 
            Enumeration size_i_and_smaller_subsets = ret.elements();
            while (size_i_and_smaller_subsets.hasMoreElements()) {
                // System.out.println("In middle loop, ret == " + ret);
                Object s = size_i_and_smaller_subsets.nextElement();
                JMLObjectSet subset = (JMLObjectSet)s;
                Enumeration elems = elements();
                while (elems.hasMoreElements()) {
                    Object o = elems.nextElement();
                    // System.out.println(this + ".powerSet() inserting " + o);
                    if (o == null) {
                        ret = ret.insert(subset.insert(null));
                    } else {
                        ret = ret.insert(subset.insert((Object)o));
                    }
                }
            }
        }
        return ret;
    }

    /** Return a new JMLObjectBag containing all the elements of this.
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall Object o;; 
      @                         \result.count(o) == 1 <==> this.has(o));
      @ implies_that
      @    ensures \result != null && (containsNull <==> \result.containsNull);
      @*/
    public /*@ non_null @*/ JMLObjectBag toBag() {
        JMLObjectBag ret = new JMLObjectBag();
        JMLObjectSetEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            Object e = (o == null ? null :  o);
            ret = ret.insert(e);
        }
        return ret;
    } 

    /** Return a new JMLObjectSequence containing all the elements of this.
     *  @see #toBag()
     *  @see #toArray()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall Object o;; 
      @                         \result.count(o) == 1 <==> this.has(o));
      @ implies_that
      @    ensures \result != null && (containsNull <==> \result.containsNull);
      @*/
    public /*@ non_null @*/ JMLObjectSequence toSequence() {
        JMLObjectSequence ret = new JMLObjectSequence();
        JMLObjectSetEnumerator enum = elements();
        while (enum.hasMoreElements()) {
            Object o = enum.nextElement();
            Object e = (o == null ? null :  o);
            ret = ret.insertFront(e);
        }
        return ret;
    } 

    /** Return a new array containing all the elements of this.
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_size()
      @         && (\forall Object o;;
      @                   JMLArrayOps.hasObjectIdentity(\result, o) <==> has(o));
      @    ensures_redundantly \result != null && \result.length == int_size()
      @         && (\forall int i; 0 <= i && i < \result.length;
      @               JMLArrayOps.hasObjectIdentity(\result, \result[i])
      @                    == has(\result[i]));
      @ implies_that
      @    ensures \result != null
      @        && (containsNull <==> !\nonnullelements(\result));
      @*/
    public /*@ non_null @*/ Object[] toArray() {
        Object[] ret = new Object[int_size()];
        JMLObjectSetEnumerator enum = elements();
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
    // The elements and toString methods are of no value for writing
    // assertions in JML. They are included for the use of developers
    // of CASE tools based on JML, e.g., type checkers, assertion
    // evaluators, prototype generators, test tools, ... . They can
    // also be used in model programs in specifications.

    /** Returns an Enumeration over this set.
     *  @see #iterator()
     */
    /*@  public normal_behavior
      @     ensures \fresh(\result) && this.equals(\result.uniteratedElems);
      @ implies_that
      @    ensures \result != null
      @        && (containsNull == \result.returnsNull);
      @*/
    public /*@ non_null @*/ JMLObjectSetEnumerator elements() {
        return new JMLObjectSetEnumerator(this);
    }  

    /** Returns an Iterator over this set.
     *  @see #elements()
     */
    /*@ also
      @    public normal_behavior
      @      ensures \fresh(\result)
      @          && \result.equals(new JMLEnumerationToIterator(elements()));
      @*/  
    public JMLIterator iterator() {
        return new JMLEnumerationToIterator(elements());
    }  

    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures (* \result is a string representation of this *);
      @*/    
    public String toString() {
        String newStr = new String("{");
        JMLListObjectNode setWalker = the_list;
        if (setWalker != null) {
            newStr = newStr + setWalker.val;
            setWalker = setWalker.next;
        }
        while (setWalker != null) {
            newStr = newStr + ", " + setWalker.val;
            setWalker = setWalker.next;
        }   
        newStr = newStr + "}";
        return newStr;
    }

}
