// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.Name;


public final class ArraySort extends AbstractSort {

    private static final WeakHashMap<SortKey, WeakReference<ArraySort>> aSH 
    	= new WeakHashMap<SortKey, WeakReference<ArraySort>>();
    
    /** keeping this key is important to prevent for too early hashmap removal*/
    private final SortKey sk;    
    
    private final ArrayOfSort commonJavaSorts;
    


    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
        
    private ArraySort(SetOfSort extendsSorts, SortKey sk) {
	super(new Name(sk.elemSort.name()+"[]"), extendsSorts, false);
	assert(!extendsSorts.isEmpty());	

	this.sk = sk;

	final Sort[] commons = new Sort[3];
	commons[0] = this.sk.javaLangObjectSort;
	commons[1] = this.sk.javaLangCloneable;
	commons[2] = this.sk.javaLangSerializable;
	commonJavaSorts = new ArrayOfSort(commons);
    }    


    

    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 


    private static SetOfSort getArraySuperSorts(Sort elemSort, 
	    					Sort objectSort, 
	    					Sort cloneableSort,
	    					Sort serializableSort) {
	SetOfSort result = SetAsListOfSort.EMPTY_SET;
	
	SetOfSort elemDirectSuperSorts = elemSort.extendsSorts();
	if(elemDirectSuperSorts.isEmpty()) {
	    result = result.add(objectSort)
	                   .add(cloneableSort)
	                   .add(serializableSort);    
	} else {
	    for(Sort s : elemDirectSuperSorts) {
		result = result.add(getArraySort(s,
						 objectSort,
						 cloneableSort,
						 serializableSort));
	    }
	}

	return result;
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 

    
    /** 
     * returns elemSort([])^n.
     */
    public static Sort getArraySortForDim(Sort elemSort, 
	    				  int n,
	    				  Sort objectSort, 
	    				  Sort cloneableSort, 
	    				  Sort serializableSort) {
	Sort result = elemSort;
	while(n > 0){
	    result = getArraySort(result, 
		    		  objectSort, 
		    		  cloneableSort, 
		    		  serializableSort);
	    n--;
	}
	return result;
    }    
    


    /**
     * returns the ArraySort to the given elementsort. This method ensures that
     * only one ArraySort-object exists for each Arraysort.
     */
    public static ArraySort getArraySort(Sort elemSort, 
	    				 Sort objectSort, 
	    				 Sort cloneableSort,
	    				 Sort serializableSort) {
	// this wrapper is required as some element sorts are shared among 
	// several environments (int, boolean)
	final SortKey sortKey = new SortKey(elemSort, 
					    objectSort, 
					    cloneableSort, 
					    serializableSort);
	ArraySort as = aSH.containsKey(sortKey) 
	               ? aSH.get(sortKey).get()
	               : null;          

	if(as == null) { 
	    SetOfSort localExtendsSorts 
	    	= getArraySuperSorts(elemSort, 
	    		             objectSort,
	    		             cloneableSort, 
	    		             serializableSort);
	    as = new ArraySort(localExtendsSorts, sortKey);
	    aSH.put(sortKey, new WeakReference<ArraySort>(as));
	}
	return as;
    }



    /**
     * @return an object of this class with elementSort().equals(p),
     * or null if such an object cannot be constructed (as p is an
     * incompatible sort).
     */
    public Sort cloneFor(Sort p) {
        return getArraySort ( p, 
        		      commonJavaSorts.getSort(0), 
        		      commonJavaSorts.getSort(1), 
        		      commonJavaSorts.getSort(2));
    }


    /**
     * returns the element sort of the array
     */
    public Sort elementSort() {
        return sk.elemSort;
    }
       
    
    private static final class SortKey {
	final Sort elemSort;
	final Sort javaLangObjectSort;
	final Sort javaLangSerializable;
	final Sort javaLangCloneable;

	public SortKey(Sort elemSort, 
		       Sort javaLangObjectSort, 
		       Sort javaLangCloneable, 
		       Sort javaLangSerializable) {         
	    this.elemSort = elemSort;
	    this.javaLangObjectSort = javaLangObjectSort;            
	    this.javaLangCloneable = javaLangCloneable;
	    this.javaLangSerializable = javaLangSerializable;
	}


	public boolean equals(Object o) {
	    if (!(o instanceof SortKey)) {
		return false;
	    }
	    final SortKey sk = (SortKey) o;
	    return elemSort == sk.elemSort 
	           && javaLangObjectSort == sk.javaLangObjectSort 
	           && javaLangSerializable == sk.javaLangSerializable 
	           && javaLangCloneable    == sk.javaLangCloneable;                
	}

	
	public int hashCode() {
	    return elemSort.hashCode() 
	           + (javaLangCloneable == null ? 0 : 31*javaLangCloneable.hashCode()) 
	           + (javaLangObjectSort == null ? 0 : 17*javaLangObjectSort.hashCode()) 
	           + (javaLangSerializable == null ? 0 : 3*javaLangSerializable.hashCode());
	}
    }
}
