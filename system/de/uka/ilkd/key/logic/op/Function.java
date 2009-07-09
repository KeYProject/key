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


public abstract class Function extends AbstractSortedOperator {
        
    /** the null pointer */
    public static final Function NULL = new RigidFunction(new Name("null"),
        					     Sort.NULL, 
        					     new Sort[0]);

    /** creates a Function 
     * @param name String with name of the function
     * @param sort the Sort of the function (result type)
     * @param argSorts ArrayOfSort of the function's arguments
     */   
    public Function(Name name, Sort sort, ArrayOfSort argSorts) {
	super(name, argSorts, sort);
    }    
    
    
    /** creates a Function 
     * @param name String with name of the function
     * @param sort the Sort of the function (result type)
     * @param argSorts an array of Sort with the sorts of 
     * the function's arguments  
     */   
    public Function(Name name, Sort sort, Sort[] argSorts) {
	super(name, new ArrayOfSort(argSorts), sort);
    }

  
    public String toString() {
	return (name()+((sort()==Sort.FORMULA)? "" : ":"+sort()));
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
