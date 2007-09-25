// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic.dfinfo;

import de.uka.ilkd.key.logic.ListOfName;
import de.uka.ilkd.key.logic.Name;


/** This class represents a set of dynamic functions.
 *
 * As the number of dynamic function is finite and we
 * need to compute fast intersection, we choose a representation
 * with a array of boolean, each boolean saying if a element
 * is a member or not of the set.
 *
 * The name information is, for space efficiency reasons, saved
 * in the factory producing the DFInfoImpl objects.
 *
 * As the number of function can grow, we need to be able to
 * add new booleans in the array. Of course, we need to expand
 * the array with 'false'. this feature is only accessible
 * for the factory, as the factory is responsible for the
 * "consistent" state of all the DFInfoImpl.
 *
 * @author Stanislas Nanchen
 */

public class DFInfo {

    private DFInfoFactory factory;

    /** the array of booleans simulating the appartenance function.
     * the ordering of elements is in the factory.
     */
    boolean[] members; 
    
    /** the current size of the info. */
    int size;

    public DFInfo(DFInfoFactory factory) {
	this.factory = factory;
    }

    public DFInfo(DFInfoFactory factory, boolean[] members) {
	this(factory);
	this.members = members;
    }

    boolean isEqual(boolean[] info) {
	if(size < info.length) {
	    setSize(info.length);
	} else if (info.length < size) {
	    // ERROR, must throw an exception.
	}
	
	for(int i=0; i<size; i++) {
	    if (members[i] != info[i]) { return false; }
	}
	return true;
    }

    private void setSize (int newSize) {
	boolean[] temp;
	
	if (newSize != size) {
	    temp = new boolean[newSize];
	    for(int i=0; i<((newSize<size)?newSize:size); i++) {
		temp[i] = members[i];
	    }
	    if (newSize > size) {
		for(int i=size; i<newSize; i++) {
		    temp[i] = false;
		}
	    }
	    members = temp;
	    size = newSize;
	}
    }

    public boolean isEqual(DFInfo info) {
	/* This is correct, as we use the flyweight pattern */
	return this==info;
    }

    public DFInfo intersect(DFInfo info) throws DFException {
	boolean[] temp, info1, info2;
	int min, max;
	/* first, we adjust the size of both infos.*/
	if (size<info.size) {
	    setSize(info.size);
	} else if (info.size<size) {
	    info.setSize(size);
	}

	/* we compute the intersection. */
	temp = new boolean[size];

	for (int i=0; i<size; i++) {
	    temp[i] = this.members[i] && info.members[i];
	}
	
	/* we call the factory to get the info who corresponds to
	 * the computed boolean array.
	 */
	return factory.getDFInfo(temp);
    }

    public DFInfo union(DFInfo info) throws DFException {
	boolean[] temp, info1, info2;
	int min, max;
	/* first, we adjust the size of both infos.*/
	if (size<info.size) {
	    setSize(info.size);
	} else if (info.size<size) {
	    info.setSize(size);
	}

	/* we compute the intersection. */
	temp = new boolean[size];

	for (int i=0; i<size; i++) {
	    temp[i] = this.members[i] || info.members[i];
	}
	
	/* we call the factory to get the info who corresponds to
	 * the computed boolean array.
	 */
	return factory.getDFInfo(temp);
    }

    public ListOfName getDynFunctionNames() {
	return factory.getDynFunctionNames(this.members);
    }

    public boolean containsName(Name function) {
	return factory.containsName(this.members, function);
    }

}
