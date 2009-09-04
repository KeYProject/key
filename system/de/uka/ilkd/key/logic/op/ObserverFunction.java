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
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


public class ObserverFunction extends Function {
            
    private final KeYJavaType container;
    private final boolean isStatic;
    private final ImmutableArray<KeYJavaType> paramTypes;

    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------     

    public ObserverFunction(Name name, 
	            	    Sort sort, 
	            	    Sort heapSort,
	            	    KeYJavaType container,
	            	    boolean isStatic,	            	    
	            	    ImmutableArray<KeYJavaType> paramTypes) {
	super(name, sort, getArgSorts(heapSort, 
				      container, 
				      isStatic, 
				      paramTypes));
	this.container = container;
	this.isStatic = isStatic;
	this.paramTypes = paramTypes;
    }
    
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private static Sort[] getArgSorts(Sort heapSort,
	    			      KeYJavaType container, 
	                              boolean isStatic, 
	                              ImmutableArray<KeYJavaType> paramTypes) {
       final int arity = isStatic 
                         ? paramTypes.size() + 1 
                         : paramTypes.size() + 2;       
       
       final Sort[] result = new Sort[arity];
       result[0] = heapSort;
 
       final int offset;
       if(isStatic) {  
           offset = 1;
       } else {
           result[1] = container.getSort();
           assert result[1] != null : "Bad KJT: " + container;
           offset = 2;
       }
       
       for(int i = 0, n = paramTypes.size(); i < n; i++) {
	   result[i + offset] = paramTypes.get(i).getSort();
       }
       
       return result;	
    }
        

    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public final KeYJavaType getContainerType() {
	return container;
    }
    
    
    public final boolean isStatic() {
	return isStatic;
    }
    
    
    public final int getNumParams() {
	return paramTypes.size();
    }
    
    
    public final KeYJavaType getParamType(int i) {
	return paramTypes.get(i);
    }
    
    
    public final ImmutableArray<KeYJavaType> getParamTypes() {
	return paramTypes;
    }
}
