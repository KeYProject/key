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
interface AbstractMap{

    //@ model instance int defaultValue;
    //@ model instance int[] contents;

    //@ initially (\forall int i; 0 <= i; contents[i] == defaultValue);

    /** Set the value of key; add it if it is not in the map yet */
    //@ requires key >= 0;
    //@ ensures contents[key] == value;
    public void replace (int key, int value);

    /** Remove key from the map */
    //@ requires key >= 0;
    //@ ensures contents[key] == defaultValue;
    public void remove (int key);

    /** Lookup the key; if it is not in the map, return the default value */
    //@ requires key >= 0;
    //@ ensures \result == contents[key];
    public /*@ pure @*/ int lookup (int key);
}
