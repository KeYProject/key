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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;


public class Function extends AbstractSortedOperator {
        
    /** the null pointer */
    public static final Function NULL = new Function(new Name("null"),
        					     Sort.NULL, 
        					     new Sort[0]);
    
    private final boolean unique;
    

    public Function(Name name, 
	            Sort sort, 
	            ArrayOfSort argSorts, 
	            boolean unique) {
	super(name, argSorts, sort);
	this.unique = unique;
    }
    
    public Function(Name name, 
	    	    Sort sort, 
	    	    Sort[] argSorts, 
	    	    boolean unique) {
	this(name, sort, new ArrayOfSort(argSorts), unique);
    }    
    

    public Function(Name name, Sort sort, ArrayOfSort argSorts) {
	this(name, sort, argSorts, false);
    }    
    
    
    public Function(Name name, Sort sort, Sort[] argSorts) {
	this(name, sort, argSorts, false);
    }
    
    
    @Override
    public boolean isRigid() {
	return true;
    }


    @Override
    public String toString() {
	return (name()+((sort()==Sort.FORMULA)? "" : ":"+sort()));
    }
    
    
    public boolean isUnique() {
	return unique;
    }    
    

    public String proofToString() {
       String s = null;
       if (sort() != null) {
	   s = (sort() == Sort.FORMULA ? "" : sort().toString()) + " ";
	   s += name();
       } else {
	   s = "NO_SORT"+" "+name();
       }
       if (arity()>0) {
          int i = 0;
          s+="(";
          while (i<arity()) {
             if (i>0) s+=",";
             s+=argSort(i);
             i++;
          }
          s+=")";
       }
       s+=";\n";
       return s;
    }
}
