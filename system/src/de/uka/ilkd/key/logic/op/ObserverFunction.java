// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Objects of this class represent "observer" function or predicate symbols.
 * An observer symbol is a symbol taking a heap array as its first argument,
 * and an object as its second argument (unless it is static). Observer
 * symbols are used to represent JML model fields as well as occurrences of
 * pure methods in specifications (via the subclass ProgramMethod). As they
 * come from the Java program, both their parameter sorts and their result 
 * sorts always have an associated KeYJavaType. Observer symbols serve as
 * the targets of contracts (i.e., as the subjects that the contracts are
 * about).
 */
public class ObserverFunction extends Function implements IObserverFunction {
            
    private final KeYJavaType container;
    private final boolean isStatic;
    private final ImmutableArray<KeYJavaType> paramTypes;
    private final KeYJavaType type;

    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------     

    public ObserverFunction(String baseName, 
	            	    Sort sort,
	            	    KeYJavaType type,	            	    
	            	    Sort heapSort,
	            	    KeYJavaType container,
	            	    boolean isStatic,	            	    
	            	    ImmutableArray<KeYJavaType> paramTypes) {
	super(new ProgramElementName(baseName, 
		                     container.getSort().toString()),
              sort, 
              getArgSorts(heapSort, container, isStatic, paramTypes));
	assert type == null || type.getSort() == sort;
	assert container != null;	
	this.type = type;
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
        
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IObserverFunction#getType()
    */
    @Override
   public final KeYJavaType getType() {
	return type;
    }
    
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IObserverFunction#getContainerType()
    */
    @Override
   public final KeYJavaType getContainerType() {
	return container;
    }
    
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IObserverFunction#isStatic()
    */
    @Override
   public final boolean isStatic() {
	return isStatic;
    }
    
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IObserverFunction#getNumParams()
    */
    @Override
   public final int getNumParams() {
	return paramTypes.size();
    }
    
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IObserverFunction#getParamType(int)
    */
    @Override
   public final KeYJavaType getParamType(int i) {
	return paramTypes.get(i);
    }
    
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IObserverFunction#getParamTypes()
    */
    @Override
   public final ImmutableArray<KeYJavaType> getParamTypes() {
	return paramTypes;
    }
}
