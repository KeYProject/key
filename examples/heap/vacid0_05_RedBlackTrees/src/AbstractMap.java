// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package vacid0.redblacktree;

/**
 * Mutable map interface without data structure exposure.
 * @author bruns
 *
 */
public interface AbstractMap{

    //@ final model instance int defaultValue;
    //@ model instance \seq contents;
    //@ model instance \locset footprint;
    
    //@ model instance boolean isEmpty;
    //@ represents isEmpty = (\forall int i; 0 <= i; contents[i] == defaultValue);

    //@ initially isEmpty;
    
    //@ accessible \inv : footprint;
    //@ accessible contents : footprint;
    //@ accessible footprint : footprint;
    //@ invariant (\forall AbstractMap x; x != this; \disjoint(footprint,x.footprint));

    /** Set the value of key; add it if it is not in the map yet */
    /*@ normal_behavior
      @ requires key >= 0;
      @ ensures contents == \seq_put(\old(contents),key,value);
      @ assignable footprint;
      @*/
    public void replace (int key, int value);

    /** Remove key from the map */
    /*@ normal_behavior
      @ requires key >= 0;
      @ ensures contents == \seq_put(\old(contents),key,defaultValue);
      @ assignable footprint;
      @*/
    public void remove (int key);

    /** Lookup the key; if it is not in the map, return the default value */
    /*@ normal_behavior
      @ requires key >= 0;
      @ ensures \result == contents[key];
      @*/
    public /*@ pure @*/ int lookup (int key);
}
