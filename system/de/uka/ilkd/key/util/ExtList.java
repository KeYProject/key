// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;


import java.util.Iterator;
import java.util.LinkedList;


/** extends java.util.LinkedList in order to collect elements
 * according to their type */
public class ExtList extends LinkedList {

    public ExtList() {
	super();
    }

    /** copies list to array (array has type of cl) */
    private Object toArray(Class cl, LinkedList list) {
	Object array=java.lang.reflect.Array.newInstance(cl,list.size());
	System.arraycopy(list.toArray(),0,array,0,list.size());
	return array;
    }

    /**
     * collects elements of the classtype cl and returns a typed array
     * @param cl Class the type of the elements that are selected
     * @return array with type cl
     */
    public Object collect(Class cl) {
	LinkedList colls=new LinkedList();
	Iterator it=iterator();
	while(it.hasNext()) {
	    Object next=it.next();
	    if (cl.isInstance(next) && (next!=null)) {
		colls.add(next);
	    }	    
	}

	return toArray(cl,colls); 

    }
    
    /**
     * returns first element in list of type cl
     * @param cl the type to be searched in list
     * @return the first element with type cl in list
     */
    public Object get(Class cl) {
	Iterator it=iterator();
	while(it.hasNext()) {
	    Object next=it.next();
	    if (cl.isInstance(next) && (next!=null)) {
		return next;
	    }	    
	}
	
	return null; 
    }

    /**
     * returns first element in list of type cl and removes the found
     * element from the list if the elemnt has not been found <tt>null</tt>
     * is returned
     * @param cl the type to be searched in list
     * @return the first element with type cl in list
     */
    public Object removeFirstOccurrence(Class cl) {
	Iterator it = iterator();
	while(it.hasNext()) {
	    Object next = it.next();
	    if (cl.isInstance(next) && (next!=null)) {
		it.remove();
		return next;
	    }	    
	}
	
	return null; 
    }


}
