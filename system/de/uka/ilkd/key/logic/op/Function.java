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

import de.uka.ilkd.key.collection.ArrayOfBoolean;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;


public class Function extends AbstractSortedOperator {
            
    private final boolean unique;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------     

    public Function(Name name, 
	            Sort sort, 
	            ArrayOfSort argSorts, 
	            ArrayOfBoolean whereToBind,
	            boolean unique) {
	super(name, argSorts, sort, whereToBind, true);
	this.unique = unique;
	assert sort != Sort.UPDATE;
	assert !(unique && sort == Sort.FORMULA);
	assert !(sort instanceof NullSort) || name.toString().equals("null")
	       : "Functions with sort \"null\" are not allowed: " + this;
    }
    
    
    public Function(Name name, 
	    	    Sort sort, 
	    	    Sort[] argSorts, 
	    	    Boolean[] whereToBind,
	    	    boolean unique) {
	this(name, 
             sort, 
             new ArrayOfSort(argSorts), 
             whereToBind == null ? null : new ArrayOfBoolean(whereToBind), 
             unique);
    }
    

    public Function(Name name, Sort sort, ArrayOfSort argSorts) {
	this(name, sort, argSorts, null, false);
    }    
    
    
    public Function(Name name, Sort sort, Sort[] argSorts) {
	this(name, sort, argSorts, null, false);
    }
    
    
    public Function(Name name, Sort sort) {
	this(name, sort, new ArrayOfSort(), null, false);
    }    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------     
    
    public boolean isUnique() {
	return unique;
    }
    

    @Override
    public String toString() {
	return (name() + (whereToBind() == null 
		          ? "" 
		          : "{" + whereToBind() + "}"));
    }
    

    public String proofToString() {
       String s =
	   (sort() == Sort.FORMULA ? "" : sort().toString()) + " ";
       s += name();
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
