// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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



public class ArraySortImpl extends AbstractCollectionSort implements ArraySort{

    private static WeakHashMap aSH = new WeakHashMap();
    
    private final ArrayOfSort commonJavaSorts;  
    
    private SetOfSort extendsSorts;
    
    /** keeping this key is important to prevent for too early hasmap removal*/
    private final SortKey sk;
    


    private ArraySortImpl(SetOfSort extendsSorts, 			  
                          SortKey sk) {
	super(sk.elemSort.name()+"[]", sk.elemSort);
	
        this.sk = sk;
        
        final Sort[] commons = new Sort[3];
        commons[0] = this.sk.javaLangObjectSort;
	commons[1] = this.sk.javaLangCloneable;
        commons[2] = this.sk.javaLangSerializable;
        commonJavaSorts = new ArrayOfSort(commons);
	// uncommented because of ASMKeY:
	//	Debug.assertTrue(extendsSorts!=SetAsListOfSort.EMPTY_SET);
	this.extendsSorts = extendsSorts;
    }

    /**
     * @return an object of this class with elementSort().equals(p),
     * or null if such an object cannot be constructed (as p is an
     * incompatible sort).
     */
    public Sort cloneFor ( Sort p ) {
	return getArraySort ( p, commonJavaSorts.getSort(0), 
                commonJavaSorts.getSort(1), commonJavaSorts.getSort(2));
    }

    /**
     * @return the sorts of the predecessors of this sort
     */
    public SetOfSort extendsSorts() {
	return extendsSorts;
    }

    
    /** 
     * returns elemSort([])^n.
     */
    public static Sort getArraySortForDim(Sort elemSort, int n, 
					  Sort objectSort, 
					  Sort cloneableSort, 
                                          Sort serializableSort){
	Sort result = elemSort;
	while(n>0){
	    result = getArraySort(result, objectSort, cloneableSort, serializableSort);
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
                                         Sort serializableSort){
        // this wrapper is required as some element sorts are shared among 
        // several environments (int, boolean)
        final SortKey sk = new SortKey(elemSort, objectSort, 
                cloneableSort, serializableSort);
        ArraySort as = aSH.containsKey(sk) ? 
                (ArraySort) ((WeakReference)aSH.get(sk)).get() : null;          
	
        if (as == null){ 
        // HACK: this simple handling of sort creation does not treat
        // depending symbols (i.e. ArrayOfS::instance)
	    SetOfSort localExtendsSorts = getArraySuperSorts(elemSort, objectSort,
							     cloneableSort, 
                                                             serializableSort);
	    as = new ArraySortImpl(localExtendsSorts, sk);
	    aSH.put(sk, new WeakReference(as));
	    
	} 
        return as;
    }

    private static SetOfSort getArraySuperSorts(Sort elem, 
						Sort objectSort,
						Sort cloneableSort,
                                                Sort serializableSort){
	int i = 1;
	while(elem instanceof ArraySort){
	    elem = ((ArraySort) elem).elementSort();
	    i++;
	}
	SetOfSort superSorts = elem.extendsSorts();
	
        if (elem instanceof PrimitiveSort || elem == objectSort){
	    i--;
	    superSorts = 
                superSorts.add(objectSort).add(cloneableSort).add(serializableSort);
	}
        
	if(i>0){
	    final IteratorOfSort it = superSorts.iterator();
	    superSorts = SetAsListOfSort.EMPTY_SET;
	    while(it.hasNext()){
		Sort s = it.next();
		superSorts = 
		    superSorts.add(getArraySortForDim(s, i, 
						      objectSort, 
						      cloneableSort, 
                                                      serializableSort));
	    }
	}
    
        return superSorts;
    }
        
    
    static class SortKey {
        final Sort elemSort;
        final Sort javaLangObjectSort;
        final Sort javaLangSerializable;
        final Sort javaLangCloneable;
        
        public SortKey(Sort elemSort, Sort javaLangObjectSort, 
                Sort javaLangCloneable, Sort javaLangSerializable) {         
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
            return elemSort == sk.elemSort &&
                javaLangObjectSort   == sk.javaLangObjectSort &&
                javaLangSerializable == sk.javaLangSerializable &&
                javaLangCloneable    == sk.javaLangCloneable;                
        }
        
        public int hashCode() {
            return elemSort.hashCode() + 
            (javaLangCloneable == null ? 0 : 31*javaLangCloneable.hashCode()) + 
            (javaLangObjectSort == null ? 0 : 17*javaLangObjectSort.hashCode()) +
            (javaLangSerializable == null ? 0 : 3*javaLangSerializable.hashCode());
        }
        
    }
}
