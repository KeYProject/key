// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt;


import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;


class SortWrapper {
    private Sort sort;
    private StringBuffer name;
    private StringBuffer predicateName;
    private LinkedList<SortWrapper> parentSorts = new LinkedList<SortWrapper>();

    public boolean extendsTrans(SortWrapper sw) {
	return sw.getSort() != getSort()
	        && getSort().extendsTrans(sw.getSort());
    }

    public Sort getSort() {
	return sort;
    }

    public StringBuffer getName() {
	return name;
    }

    public StringBuffer getPredicateName() {
	return predicateName;
    }

    public SortWrapper(Sort sort, StringBuffer name, StringBuffer predicateName) {
	super();
	this.sort = sort;
	this.name = name;
	this.predicateName = predicateName;
    }

    public LinkedList<SortWrapper> getParents() {
	return parentSorts;
    }

    void computeParentSorts(LinkedList<SortWrapper> sorts, boolean explicitNullHierarchy, boolean explicitHierarchy,
	      Services services) {
	for (SortWrapper sw : sorts) {
	    if (this.extendsTrans(sw)) {
		addParent(sw,explicitNullHierarchy,explicitHierarchy,services);
	    }
	}
    }

    /**
     * Removes all sorts from parentSorts, that are not extended by this sort
     * directly, i.e. the sort <code>parent</code> is between
     * <code>this.getSort()</code> and the considered sort.
     */
    private void removeGrandParents(SortWrapper parent) {
	Iterator<SortWrapper> it = parentSorts.iterator();
	while (it.hasNext()) {
	    SortWrapper sw = it.next();
	    if (parent.extendsTrans(sw)) {
		it.remove();
	    }
	}
    }

   private boolean addParent(SortWrapper parent, boolean explicitNullHierarchy, boolean explicitHierarchy, Services services) {
	Function nullOp = services.getTypeConverter().getHeapLDT().getNull();
	if((explicitNullHierarchy && this.getSort() == nullOp.sort())|| explicitHierarchy){
	    parentSorts.add(parent);
	    return true;
	}
	
	for (SortWrapper sw : parentSorts) {
	    // only add the sort as parent, if it is a direct super sort.
	    if (sw.extendsTrans(parent)) {
		return false;
	    }
	}
	parentSorts.add(parent);
	
	    removeGrandParents(parent);
	return true;

    }

}

/**
 * The SortHierarchy works as a wrapper class for sorts.
 * 
 * @author Simon Greiner
 * 
 */
public class SortHierarchy {

    private LinkedList<SortWrapper> sorts = new LinkedList<SortWrapper>();

    /**
     * Create a Sort Hierarchy.
     * 
     * @param sortnames
     *            a HashMap of sorts mapped to the Strings which is displayed in
     *            Formulas
     */
    protected SortHierarchy(HashMap<Sort, StringBuffer> sortnames,
	    HashMap<Sort, StringBuffer> prednames, boolean explicitNullHierarchy, boolean explicitHierarchy,
	    Services services) {
	for (Entry<Sort, StringBuffer> entry : sortnames.entrySet()) {
	    sorts.add(new SortWrapper(entry.getKey(), entry.getValue(),
		    prednames.get(entry.getKey())));
	}

	for (SortWrapper sw : sorts) {
	    sw.computeParentSorts(sorts,explicitNullHierarchy,explicitHierarchy,services);
	}

    }

    public LinkedList<SortWrapper> getSorts() {
	return sorts;
    }

}