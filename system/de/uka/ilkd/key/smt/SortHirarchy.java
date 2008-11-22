package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The SortHirarchy works as a wrapper class fot sorts.
 * @author Simon Greiner
 *
 */
public class SortHirarchy {

    private HashMap<Sort, StringBuffer> sortMap;

    private HashMap<Sort, StringBuffer> predicateMap;

    private HashMap<Sort, ArrayList<Sort>> directSuperSortList;

    /**
     * Create a Sort Hirarchy.
     * @sortnames A hashmap of sorts mapped to the Strings which
     *      is displayed in Formulas
     *
     */
    protected SortHirarchy(HashMap<Sort, StringBuffer> sortnames,
	    HashMap<Sort, StringBuffer> prednames) {
	this.sortMap = sortnames;
	this.predicateMap = prednames;
	this.directSuperSortList = this.getDirectSuperSorts();
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
	    //                      get all sorts, that are supersort of s
	    ArrayList<Sort> extended = new ArrayList<Sort>();
	    for (Sort t : sortMap.keySet()) {
		if (s != t && s.extendsTrans(t)) {
		    extended.add(t);
		}
	    }
	    supersortList.put(s, extended);
	    /*                        for (Sort t : s.extendsSorts()) {
	     extended.add(t);
	     }
	     if (s.extendsSorts().size() > 0) {
	     
	     //remove all sorts, that are not direct super sort
	     for (int i = 0; i < extended.size(); ) {
	     Sort toBeChecked1 = extended.get(i);
	     boolean isExtended = false;
	     for (int j = i; j < extended.size() && !isExtended; ) {
	     Sort toBeChecked2 = extended.get(j);
	     if (toBeChecked1.extendsTrans(toBeChecked2)) {
	     //toBeChecked2 is supersort of toBeChecked1
	     extended.remove(j);
	     } else if (toBeChecked2.extendsTrans(toBeChecked1)) {
	     isExtended = true;
	     } else {
	     j++;
	     }
	     
	     }
	     if (isExtended) {
	     extended.remove(i);
	     } else {
	     i++;
	     }
	     }
	     }*/

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

	HashMap<Sort, ArrayList<Sort>> hirarchy = this.getDirectSuperSorts();

	HashMap<StringBuffer, ArrayList<StringBuffer>> toReturn = new HashMap<StringBuffer, ArrayList<StringBuffer>>();
	for (Sort s : hirarchy.keySet()) {
	    ArrayList<Sort> extended = hirarchy.get(s);
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

	HashMap<Sort, ArrayList<Sort>> hirarchy = this.getDirectSuperSorts();

	HashMap<StringBuffer, ArrayList<StringBuffer>> toReturn = new HashMap<StringBuffer, ArrayList<StringBuffer>>();
	for (Sort s : hirarchy.keySet()) {
	    ArrayList<Sort> extended = hirarchy.get(s);
	    ArrayList<StringBuffer> supersorts = new ArrayList<StringBuffer>();
	    for (Sort t : extended) {
		supersorts.add(predicateMap.get(t));
	    }
	    toReturn.put(predicateMap.get(s), supersorts);
	}
	return toReturn;
    }

}
