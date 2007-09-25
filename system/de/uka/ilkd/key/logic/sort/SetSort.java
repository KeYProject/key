// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.ListOfSortDependingSymbol;
import de.uka.ilkd.key.logic.op.SLListOfSortDependingSymbol;
import de.uka.ilkd.key.logic.op.SortDependingFunction;


public class SetSort extends AbstractCollectionSort {
    
    /** creates a Sort (with a new equality symbol for this sort) */
    protected SetSort(de.uka.ilkd.key.logic.sort.Sort elemSort) {
	super(elemSort.name() + "{}", elemSort);        
    }

    /**
     * @return an object of this class with elementSort().equals(p),
     * or null if such an object cannot be constructed (as p is an
     * incompatible sort)
     */
    public Sort cloneFor ( Sort p ) {
	if ( p instanceof AbstractNonCollectionSort )
	    return ((AbstractNonCollectionSort)p).getSetSort ();
	else
	    return null;
    }
  
    protected void createSymbols (Namespace p_func_ns, Namespace sort_ns) {
	if(!symbolsCreated) {
	    super.createSymbols(p_func_ns, sort_ns);
	    
	    ListOfSortDependingSymbol res = SLListOfSortDependingSymbol.EMPTY_LIST;
              	
	    final Sort intSort = (Sort)sort_ns.lookup(new Name("int"));	
	    if ( intSort == null ){
        	return;
    	    }
            
            res = createSymbol ( res, "size",                intSort,
        	  	         new Sort[] { this } );
               
            if (elementSort() == intSort) {
                res = createSymbol ( res, "sum", intSort,
            			 new Sort[] { this  } );
            }
        
            res = createSymbol ( res, "count", intSort,
        	    	     new Sort[] { this, elementSort() } );
            
            res = createSymbol ( res, "union",               this,
            		     new Sort[] { this, this } );
            res = createSymbol ( res, "intersection",        this,
            		     new Sort[] { this, this } );
            res = createSymbol ( res, "without",             this,
            		     new Sort[] { this, this } );
            res = createSymbol ( res, "symmetricDifference", this,
            		     new Sort[] { this, this } );
            res = createSymbol ( res, "including",           this,
            		     new Sort[] { this, elementSort () } );
            
            res = createSymbol ( res, "excluding",           this,
            		     new Sort[] { this, elementSort () } );
            
            res = createSymbol ( res, "includes",            Sort.FORMULA,
            		     new Sort[] { this, elementSort () } );
            res = createSymbol ( res, "excludes",            Sort.FORMULA,
            		     new Sort[] { this, elementSort () } );
            res = createSymbol ( res, "isEmpty",             Sort.FORMULA,
            		     new Sort[] { this } );
            res = createSymbol ( res, "notEmpty",            Sort.FORMULA,
            		     new Sort[] { this } );
            res = createSymbol ( res, "emptySet",            this,
            	             new Sort [0] );
            
            addSymbols(res);
	}
    }

    private ListOfSortDependingSymbol createSymbol
	( ListOfSortDependingSymbol p_list,
	  String                    p_name,
	  Sort                      p_valueSort,
	  Sort[]                    p_argSorts ) {

	Name kind     = new Name ( "Set::" + p_name );
	Name fullname = new Name ( elementSort ().name () + "{}" +
            "::" + p_name );

	SortDependingFunction f = new SortDependingFunction ( fullname,
							      p_valueSort,
							      p_argSorts,
							      kind,
							      elementSort () );

	return p_list.prepend ( f );
    }

}
