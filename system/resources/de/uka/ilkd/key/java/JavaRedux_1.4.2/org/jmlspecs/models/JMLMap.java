// @(#)$Id: JMLMap.java 1.2 Wed, 25 May 2005 14:55:29 +0200 engelc $

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

/** Maps (i.e., binary relations that are functional) from non-null
 *  elements of {@link _DomainType_} to non-null elements of {@link
 *  _RangeType_}.  The first type, <kbd>_DomainType_</kbd>, is called
 *  the domain type of the map; the second type,
 *  <kbd>_RangeType_</kbd>, is called the range type of the map.  A
 *  map can be seen as a set of pairs, of form <em>(dv, rv)</em>,
 *  consisting of an element of the domain type, <em>dv</em>, and an
 *  element of the range type, <em>rv</em>.  Alternatively, it can be
 *  seen as a function that maps each element of the domain to some of
 *  elements of the range type.
 *
 *  <p> This type is a subtype of {@link
 *  JML_Domain_To_Range_Relation}, and as such as can be treated as a
 *  binary relation or a set valued function also.  See the
 *  documentation for {@link JML_Domain_To_Range_Relation} and for the
 *  methods inherited from this supertype for more information.
 *
 *  <p> This type considers elements <kbd>val</kbd> and <kbd>dv</kbd>
 *  of the domain type, to be distinct just when
 *  <kbd>_val_not_equal_to_dv_</kbd>.  It considers elements of
 *  <kbd>r</kbd> and <kbd>rv</kbd> of the range type to be distinct
 *  just when <kbd>_r_not_equal_to_rv_</kbd>.  Cloning takes place for
 *  the domain or range elements if the corresponding domain or range
 *  type is {@link JMLType}.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens
 * @author Clyde Ruby
 * @see JMLCollection
 * @see JMLType
 * @see JML_Domain_To_Range_Relation
 * @see JML_Domain_To_Range_RelationEnumerator
 * @see JML_Domain_To_Range_RelationImageEnumerator
 * @see JMLValueSet
 * @see JMLObjectSet
 * @see JMLObjectToObjectMap
 * @see JMLValueToObjectMap
 * @see JMLObjectToValueMap
 * @see JMLValueToValueMap
 * @see JML_Domain_To_Range_Relation#toFunction()
 */
//-@ immutable
public /*@ pure @*/
class JML_Domain_To_Range_Map extends JML_Domain_To_Range_Relation {

    /*@ public invariant isaFunction();
      @ public invariant_redundantly
      @        (\forall _DomainType_ dv; isDefinedAt(dv);
      @                                  elementImage(dv).int_size() == 1);
      @*/

    /** Initialize this map to be the empty mapping.
     * @see #EMPTY
     */
    /*@  public normal_behavior
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures theRelation.equals(new JMLValueSet());
      @    ensures_redundantly theRelation.isEmpty();
      @*/
    public JML_Domain_To_Range_Map() 
    {
        super();
    }

    /** Initialize this map to be a mapping that maps the given domain
     * element to the given range element.
     * @see #singletonMap(_DomainType_, _RangeType_)
     * @see #JML_Domain_To_Range_Map(JML_Domain__Range_Pair)
     */
    /*@  public normal_behavior
      @    requires dv != null && rv != null;
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures (theRelation.int_size() == 1) && elementImage(dv).has(rv);
      @    ensures_redundantly isDefinedAt(dv);
      @*/
    public JML_Domain_To_Range_Map(/*@ non_null @*/ _DomainType_ dv,
                                   /*@ non_null @*/ _RangeType_ rv)
    {
        super(dv, rv);
    }

    /** Initialize this map to be a mapping that maps the key in the
     * given pair to the value in that pair.
     * @see #singletonMap(JML_Domain__Range_Pair)
     * @see #JML_Domain_To_Range_Map(_DomainType_, _RangeType_)
     */
    /*@  public normal_behavior
      @    requires pair != null;
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures (theRelation.int_size() == 1)
      @         && elementImage(pair.key).has(pair.value);
      @    ensures_redundantly isDefinedAt(pair.key);
      @*/
    public JML_Domain_To_Range_Map(/*@ non_null @*/
                                   JML_Domain__Range_Pair pair)
    {
        super(pair.key, pair.value);
    }

    /** Initialize this map based on the representation values given.
     */
    /*@    requires ipset != null && dom != null && 0 <= sz;
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures imagePairSet_ == ipset && domain_ == dom && size_ == sz;
      @*/
    protected JML_Domain_To_Range_Map(JMLValueSet ipset,
                                      JML_Domain_Set dom,
                                      int sz)
    {
        super(ipset, dom, sz);
    }

    /** The empty JML_Domain_To_Range_Map.
     * @see #JML_Domain_To_Range_Map()
     */
    public static final /*@ non_null @*/ JML_Domain_To_Range_Map EMPTY
        = new JML_Domain_To_Range_Map();

    /** Return the singleton map containing the given association.
     * @see #JML_Domain_To_Range_Map(_DomainType_, _RangeType_)
     * @see #singletonMap(JML_Domain__Range_Pair)
     */
    /*@ public normal_behavior
      @    requires dv != null && rv != null;
      @    ensures \result != null
      @         && \result.equals(new JML_Domain_To_Range_Map(dv, rv));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JML_Domain_To_Range_Map
        singletonMap(/*@ non_null @*/ _DomainType_ dv,
                     /*@ non_null @*/ _RangeType_ rv)
    {
        return new JML_Domain_To_Range_Map(dv, rv);
    }

    /** Return the singleton map containing the association described
     * by the given pair.
     * @see #JML_Domain_To_Range_Map(JML_Domain__Range_Pair)
     * @see #singletonMap(_DomainType_, _RangeType_)
     */
    /*@ public normal_behavior
      @    requires pair != null;
      @    ensures \result != null
      @         && \result.equals(new JML_Domain_To_Range_Map(pair));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JML_Domain_To_Range_Map
        singletonMap(/*@ non_null @*/ JML_Domain__Range_Pair pair)
    {
        return new JML_Domain_To_Range_Map(pair);
    }

    /** Tells whether this relation is a function.
     */
    /*@ also
      @    public normal_behavior
      @      ensures \result;
      @*/
    //@ pure
    public boolean isaFunction()
    {
        return true;
    }

    /** Return the range element corresponding to dv, if there is one.
     *
     * @param dv the domain element for which an association is
     * sought (the key to the table).
     * @exception JMLNoSuchElementException when dv is not associated
     * to any range element by this.
     * @see JML_Domain_To_Range_Relation#isDefinedAt
     * @see JML_Domain_To_Range_Relation#elementImage
     * @see JML_Domain_To_Range_Relation#image
     */
    /*@  public normal_behavior
      @    requires isDefinedAt(dv);
      @    ensures elementImage(dv).has(\result);
      @ also
      @  public exceptional_behavior
      @    requires !isDefinedAt(dv);
      @    signals (JMLNoSuchElementException);
      @*/
    public /*@ non_null @*/ _RangeType_ apply(_DomainType_ dv)
        throws JMLNoSuchElementException
    {
        JML_Range_Set img = elementImage(dv);
        if (img.int_size() == 1) {
            _RangeType_ res = img.choose();
            return res;
        } else {
            throw new JMLNoSuchElementException("Map not defined at " + dv);
        }
    }

    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JML_Domain_To_Range_Map
      @          && ((JML_Domain_To_Range_Map)\result)
      @                .theRelation.equals(this.theRelation);
      @*/
    //@ pure
    public Object clone() 
    {
        return new JML_Domain_To_Range_Map(imagePairSet_, domain_, size_);
    } 

    /** Return a new map that is like this but maps the given domain
     *  element to the given range element.  Any previously existing
     *  mapping for the domain element is removed first.
     * @see JML_Domain_To_Range_Relation#insert(_DomainType_, _RangeType_)
     */
    /*@  public normal_behavior
      @    requires dv != null && rv != null;
      @    requires !isDefinedAt(dv) ==> int_size() < Integer.MAX_VALUE;
      @    ensures \result.equals(this.removeDomainElement(dv).add(dv, rv));
      @*/
    public /*@ non_null @*/
        JML_Domain_To_Range_Map extend(/*@ non_null @*/ _DomainType_ dv,
                                       /*@ non_null @*/ _RangeType_ rv) 
    {
        JML_Domain_To_Range_Map newMap = this.removeDomainElement(dv);
        newMap = newMap.disjointUnion(new JML_Domain_To_Range_Map(dv, rv));
        return newMap;
    } 

    /** Return a new map that is like this but has no association for the
     *  given domain element.
     * @see JML_Domain_To_Range_Relation#removeFromDomain
     */
    /*@  public normal_behavior
      @    ensures \result.equals(removeFromDomain(dv).toFunction());
      @    ensures_redundantly !isDefinedAt(dv) ==> \result.equals(this);
      @*/
    public /*@ non_null @*/
        JML_Domain_To_Range_Map removeDomainElement(_DomainType_ dv)
    {
        return super.removeFromDomain(dv).toFunction();
    }

    /** Return a new map that is the composition of this and the given
     *  map.  The composition is done in the usual order; that is, if
     *  the given map maps x to y and this maps y to z, then the
     *  result maps x to z.
     * @see #compose(JMLObjectTo_Domain_Map)
     */
    /*@  public normal_behavior
      @    requires othMap != null;
      @    ensures (\forall JMLValue_Range_Pair pair; ;
      @                 \result.theRelation.has(pair) 
      @                    == (\exists _DomainType_ val;
      @                            othMap.elementImage(pair.key).has(val);
      @                            this.elementImage(val).has(pair.value) 
      @                            )
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLValueTo_Range_Map
        compose(/*@ non_null @*/ JMLValueTo_Domain_Map othMap)
    {
        return super.compose(othMap).toFunction();
    }

    /** Return a new map that is the composition of this and the given
     *  map.  The composition is done in the usual order; that is, if
     *  the given map maps x to y and this maps y to z, then the
     *  result maps x to z.
     * @see #compose(JMLValueTo_Domain_Map)
     */
    /*@  public normal_behavior
      @    requires othMap != null;
      @    ensures (\forall JMLObject_Range_Pair pair; ;
      @                 \result.theRelation.has(pair) 
      @                    == (\exists _DomainType_ val;
      @                            othMap.elementImage(pair.key).has(val);
      @                            this.elementImage(val).has(pair.value) 
      @                            )
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLObjectTo_Range_Map
        compose(/*@ non_null @*/ JMLObjectTo_Domain_Map othMap)
    {
        return super.compose(othMap).toFunction();
    }

    /** Return a new map that only maps elements in the given domain
     * to the corresponding range elements in this map.
     * @see #rangeRestrictedTo
     * @see JML_Domain_To_Range_Relation#restrictDomainTo
     */
    /*@  public normal_behavior
      @    requires dom != null;
      @    ensures (\forall JML_Domain__Range_Pair pair; ; 
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       dom.has(pair.key) 
      @                    && elementImage(pair.key).has(pair.value)
      @                );
      @*/
    public /*@ non_null @*/ 
        JML_Domain_To_Range_Map 
        restrictedTo(/*@ non_null @*/ JML_Domain_Set dom) 
    {
        return super.restrictDomainTo(dom).toFunction();
    }

    /** Return a new map that is like this map but only contains
     *  associations that map to range elements in the given set.
     * @see #restrictedTo
     * @see JML_Domain_To_Range_Relation#restrictRangeTo
     */
    /*@  public normal_behavior
      @    requires rng != null;
      @    ensures (\forall JML_Domain__Range_Pair pair; ;
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       rng.has(pair.value) 
      @                    && elementImage(pair.key).has(pair.value)
      @                );
      @*/
    public /*@ non_null @*/ 
        JML_Domain_To_Range_Map
        rangeRestrictedTo(/*@ non_null @*/ JML_Range_Set rng)
    {
        return super.restrictRangeTo(rng).toFunction();
    }

    /** Return a new map that is like the union of the given map and
     *  this map, except that if both define a mapping for a given domain
     *  element, then only the mapping in the given map is retained.
     * @see #clashReplaceUnion
     * @see #disjointUnion
     * @see JML_Domain_To_Range_Relation#union
     */
    /*@  public normal_behavior
      @    requires othMap != null;
      @    requires int_size()
      @             <= Integer.MAX_VALUE - othMap.difference(this).int_size();
      @    ensures (\forall JML_Domain__Range_Pair pair; ;
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       othMap.elementImage(pair.key).has(pair.value)
      @                    || (!othMap.isDefinedAt(pair.key)
      @                        && this.elementImage(pair.key).has(pair.value))
      @                );
      @*/
    public /*@ non_null @*/ 
        JML_Domain_To_Range_Map
        extendUnion(/*@ non_null @*/ JML_Domain_To_Range_Map othMap) 
        throws IllegalStateException
    {
        JML_Domain_To_Range_Map newMap 
            = this.restrictedTo(this.domain_.difference(othMap.domain_));
        if (newMap.size_ <= Integer.MAX_VALUE - othMap.size_) {
            return
                new JML_Domain_To_Range_Map(newMap.imagePairSet_
                                            .union(othMap.imagePairSet_),
                                            newMap.domain_
                                            .union(othMap.domain_),
                                            newMap.size_ + othMap.size_);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_UNION);
        }
    }

    /** Return a new map that is like the union of the given map and
     * this map, except that if both define a mapping for a given
     * domain element, then each of these clashes is replaced by a
     * mapping from the domain element in question to the given range
     * element.
     * @param othMap the other map.
     * @param errval the range element to use when clashes occur.
     * @see #extendUnion
     * @see #disjointUnion
     * @see JML_Domain_To_Range_Relation#union
     */
    /*@  public normal_behavior
      @    requires othMap != null && errval != null;
      @    requires int_size()
      @             <= Integer.MAX_VALUE - othMap.difference(this).int_size();
      @    ensures (\forall JML_Domain__Range_Pair pair; ; 
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       (!othMap.isDefinedAt(pair.key)
      @                        && this.elementImage(pair.key).has(pair.value))
      @                    || (!this.isDefinedAt(pair.key)
      @                        && othMap.elementImage(pair.key)
      @                                 .has(pair.value))
      @                    || (this.isDefinedAt(pair.key)
      @                        && othMap.isDefinedAt(pair.key)
      @                        && pair.value _rangeEquals_ (errval))
      @                );
      @ implies_that
      @    requires othMap != null && errval != null;
      @*/
    public /*@ non_null @*/ 
        JML_Domain_To_Range_Map
        clashReplaceUnion(JML_Domain_To_Range_Map othMap,
                          _RangeType_ errval)
        throws IllegalStateException
    {
        JML_Domain_Set overlap = this.domain_.intersection(othMap.domain_);
        Enumeration overlapEnum = overlap.elements();
        othMap = othMap.restrictedTo(othMap.domain_.difference(overlap));
        JML_Domain_To_Range_Map newMap
            = this.restrictedTo(this.domain_.difference(overlap));
        JML_Domain_To_Range_Relation newRel;
        if (newMap.size_ <= Integer.MAX_VALUE - othMap.size_) {
            newRel = new JML_Domain_To_Range_Relation(newMap.imagePairSet_
                                                      .union(othMap
                                                             .imagePairSet_),
                                                      newMap.domain_
                                                      .union(othMap.domain_),
                                                      newMap.size_
                                                      + othMap.size_);
        } else {
                throw new IllegalStateException(TOO_BIG_TO_UNION);
        }
        _DomainType_ dv;
        while (overlapEnum.hasMoreElements()) {
            Object oo = overlapEnum.nextElement();
            dv = (_DomainType_) oo;
            newRel = newRel.add(dv, errval);
        }
        return newRel.toFunction();
    } 

    /** Return a map that is the disjoint union of this and othMap.
     *  @param othMap the other mapping
     *  @exception JMLMapException the ranges of this and othMap have elements
     *  in common (i.e., when they interesect).
     * @see #extendUnion
     * @see #clashReplaceUnion
     * @see JML_Domain_To_Range_Relation#union
     */
    /*@  public normal_behavior
      @    requires othMap != null
      @          && this.domain().intersection(othMap.domain()).isEmpty();
      @    requires int_size() <= Integer.MAX_VALUE - othMap.int_size();
      @    ensures \result.equals(this.union(othMap));
      @ also
      @  public exceptional_behavior
      @    requires othMap != null
      @          && !this.domain().intersection(othMap.domain()).isEmpty();
      @    signals (JMLMapException);
      @*/
    public /*@ non_null @*/ 
        JML_Domain_To_Range_Map 
        disjointUnion(/*@ non_null @*/ JML_Domain_To_Range_Map othMap) 
        throws JMLMapException, IllegalStateException
    {
        JML_Domain_Set overlappingDom = domain_.intersection(othMap.domain_);
        if (overlappingDom.isEmpty()) {
            if (this.size_ <= Integer.MAX_VALUE - othMap.size_) {
                return new JML_Domain_To_Range_Map(this.imagePairSet_
                                                   .union(othMap
                                                          .imagePairSet_),
                                                   this.domain_
                                                   .union(othMap.domain_),
                                                   this.size_ + othMap.size_);
            } else {
                throw new IllegalStateException(TOO_BIG_TO_UNION);
            }
        } else {
            throw new JMLMapException("Overlapping domains in "
                                      + " disjointUnion operation",
                                      overlappingDom);
        }
    }
    
}
