// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Term;


/**
 *
 */
public interface IUpdateOperator extends Operator, NonRigid {

    /**
     * Replace the locations of this operator without changing anything else.
     * This must not change the number of locations, i.e.
     * <code>newLocs.length==locationCount()</code>
     */
    IUpdateOperator replaceLocations(Location[] newLocs);
    
    /**
     * returns the array of location operators which are updated
     */
    ImmutableArray<Location> locationsAsArray();

    /**
     * returns the number of locations
     * 
     * @return the number of locations as int
     */
    int locationCount();

    /**
     * returns the operator of <tt>n</tt>-th location
     */
    Location location(int n);

    /**
     * returns the number of the subterm representing the value to which
     * the locPos-th location is updated
     */
    int valuePos(int locPos);

    /**
     * returns an array with all location positions of <code>loc</code>
     * 
     * @param loc a n Operator accessing a location
     * @return all location positions of <code>loc</code>
     */
    int[] getLocationPos(Operator loc);

    /**
     * @return the index of the first subterm belonging to update entry
     *         <code>locPos</code>
     */
    int entryBegin(int locPos);
    
    /**
     * @return the index after the last subterm belonging to update entry
     *         <code>locPos</code>. The entry is described within
     *         <tt>[entryBegin(i), entryEnd(i))</tt>
     */
    int entryEnd (int locPos);
    
    /**
     * @return the index of the first subterm belonging to the location of entry
     *         <code>locPos</code>
     */
    int locationSubtermsBegin (int locPos);
    
    /**
     * @return the index after the last subterm belonging to the location of
     *         update entry <code>locPos</code>. The location is described
     *         within
     *         <tt>[locationSubtermsBegin(i), locationSubtermsEnd(i))</tt>
     */
    int locationSubtermsEnd (int locPos);

    /**
     * returns the n-th location of the update as term
     * 
     * @param t
     *            Term with this operator as top level operator
     * @param n
     *            an int specifying the position of the requested location
     * @return the n-th location of term t updated by this operator
     */
    Term location(Term t, int n);

    /**
     * returns value the n-th location is updated with
     * 
     * @param t
     *            Term with this operator as top level operator
     * @param n
     *            an int specifying the position of the location
     * @return the value the n-th location is updated with
     */
    Term value(Term t, int n);

    /**
     * @return the index of the subterm representing the formula/term the update
     *         is applied to
     */
    int targetPos();
    
    /**
     * return the subterm representing the formula/term the update is applied to
     * 
     * @param t
     *            Term with this operator as top level operator
     * @return the target of this update application
     */    
    Term target(Term t);
    
}
