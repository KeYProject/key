// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The SortHierarchy works as a wrapper class for sorts.
 * @author Simon Greiner
 *
 */
public class SortHierarchy {

    private HashMap<Sort, StringBuffer> sortMap;

    private HashMap<Sort, StringBuffer> predicateMap;


    /**
     * Create a Sort Hierarchy.
     * @param sortnames a HashMap of sorts mapped to the Strings which
     *      is displayed in Formulas
     */
    protected SortHierarchy(HashMap<Sort, StringBuffer> sortnames,
	    HashMap<Sort, StringBuffer> prednames) {
	this.sortMap = sortnames;
	this.predicateMap = prednames;
    }

    /**
     * Get the names of all sorts, that have no supersort.
     * @return ArrayList containing all those sorts.
     */
    protected ArrayList<StringBuffer> getTopSorts() {
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();

	for (Sort s : sortMap.keySet()) {
	    if (s.extendsSorts().size() == 0) {
		toReturn.add(sortMap.get(s));
	    }
	}

	return toReturn;
    }

    private HashMap<Sort, ArrayList<Sort>> getDirectSuperSorts() {
	HashMap<Sort, ArrayList<Sort>> supersortList = new HashMap<Sort, ArrayList<Sort>>();

	for (Sort s : sortMap.keySet()) {
	    //get all sorts, that are supersort of s
	    ArrayList<Sort> extended = new ArrayList<Sort>();
	    for (Sort t : sortMap.keySet()) {
		if (s != t && s.extendsTrans(t)) {
		    extended.add(t);
		}
	    }
	    supersortList.put(s, extended);
	}

	//remove sorts from toReturn, that are extended by another sort in toReturn
	HashMap<Sort, ArrayList<Sort>> toReturn = new HashMap<Sort, ArrayList<Sort>>();
	for (Sort s : supersortList.keySet()) {
	    ArrayList<Sort> sortlist = new ArrayList<Sort>();
	    ArrayList<Sort> currentList = supersortList.get(s);
	    for (Sort t : currentList) {
		boolean isExtended = false;
		for (Sort u : currentList) {
		    if (u != t && u.extendsTrans(t)) {
			isExtended = true;
		    }
		}
		if (!isExtended) {
		    sortlist.add(t);
		}

	    }
	    toReturn.put(s, sortlist);
	}
	return toReturn;
    }

    /**
     * get a List of all sorts and teir direct supersorts
     * @return Hashmap with the sorts name as key and their supersorts as value.
     */
    protected HashMap<StringBuffer, ArrayList<StringBuffer>> getDirectSuperSortNames() {

	HashMap<Sort, ArrayList<Sort>> hierarchy = this.getDirectSuperSorts();

	HashMap<StringBuffer, ArrayList<StringBuffer>> toReturn = new HashMap<StringBuffer, ArrayList<StringBuffer>>();
	for (Sort s : hierarchy.keySet()) {
	    ArrayList<Sort> extended = hierarchy.get(s);
	    ArrayList<StringBuffer> supersorts = new ArrayList<StringBuffer>();
	    for (Sort t : extended) {
		supersorts.add(sortMap.get(t));
	    }
	    toReturn.put(sortMap.get(s), supersorts);
	}
	return toReturn;
    }

    /**
     * get a List of sortpredicates of all sorts and their direct supersorts
     * @return Hashmap with the sorts sortpredicate as key and their supersorts as value.
     */
    protected HashMap<StringBuffer, ArrayList<StringBuffer>> getDirectSuperSortPredicate() {

	HashMap<Sort, ArrayList<Sort>> hierarchy = this.getDirectSuperSorts();

	HashMap<StringBuffer, ArrayList<StringBuffer>> toReturn = new HashMap<StringBuffer, ArrayList<StringBuffer>>();
	for (Sort s : hierarchy.keySet()) {
	    ArrayList<Sort> extended = hierarchy.get(s);
	    ArrayList<StringBuffer> supersorts = new ArrayList<StringBuffer>();
	    for (Sort t : extended) {
		supersorts.add(predicateMap.get(t));
	    }
	    toReturn.put(predicateMap.get(s), supersorts);
	}
	return toReturn;
    }

}
