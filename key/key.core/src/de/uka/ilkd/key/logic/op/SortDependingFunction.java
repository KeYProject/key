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

package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * The objects of this class represent families of function symbols, where
 * each family contains an instantiation of a template symbol for a particular
 * sort. 
 * The following invariant has to hold:
 * Given two sort depending functions f1 and f2 then
 * from f1.isSimilar(f2) and f1.getSortDependingOn() == f2.getSortDependingOn()
 * follows f1 == f2 
 */
public final class SortDependingFunction extends Function {
    
    private final SortDependingFunctionTemplate template;
    private final Sort sortDependingOn;

       
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------     
    
    private SortDependingFunction(SortDependingFunctionTemplate template,
	    			  Sort sortDependingOn) {
	super(instantiateName(template.kind, sortDependingOn), 
	      instantiateResultSort(template, sortDependingOn),
	      instantiateArgSorts(template, sortDependingOn),
	      null,
	      template.unique, false);
	this.template = template;
	this.sortDependingOn = sortDependingOn;
    }

    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private static Name instantiateName(Name kind,
	    				Sort sortDependingOn) {
	return new Name(sortDependingOn + "::" + kind);
    }
    
    
    private static Sort instantiateResultSort(
	    			SortDependingFunctionTemplate template,
	    			Sort sortDependingOn) {
	return template.sort == template.sortDependingOn
	       ? sortDependingOn
	       : template.sort;
    }
    
    
    private static ImmutableArray<Sort> instantiateArgSorts(
	    			SortDependingFunctionTemplate template,
	    			Sort sortDependingOn) {
	Sort[] result = new Sort[template.argSorts.size()];
	for(int i = 0; i < result.length; i++) {
	    result[i] 
	           = (template.argSorts.get(i) == template.sortDependingOn
		      ? sortDependingOn
		      : template.argSorts.get(i));
	}
	return new ImmutableArray<Sort>(result);
    }
    
    

 
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    public static SortDependingFunction createFirstInstance(
	    			GenericSort sortDependingOn,
	    			Name kind, 
	    		        Sort sort, 
	    		        Sort[] argSorts,
	    		        boolean unique) {
	SortDependingFunctionTemplate template 
		= new SortDependingFunctionTemplate(sortDependingOn, 
						    kind, 
						    sort, 
						    new ImmutableArray<Sort>(argSorts),
						    unique);
	return new SortDependingFunction(template, Sort.ANY);
    }
    
    
    public static SortDependingFunction getFirstInstance(Name kind,
	    					         TermServices services) {
	return (SortDependingFunction) 
			services.getNamespaces()
			        .functions()
	                        .lookup(instantiateName(kind, Sort.ANY));
    }
        

    public SortDependingFunction getInstanceFor(Sort sort, 
	    				        TermServices services) {
	if(sort == this.sortDependingOn) {
	    return this;
	}
	
	assert !(sort instanceof ProgramSVSort);
	assert sort != AbstractTermTransformer.METASORT;
	
	SortDependingFunction result
		= (SortDependingFunction) 
		      services.getNamespaces()
	                      .lookup(instantiateName(getKind(), 
	                	      		      sort));
	
	//ugly: multiple generic sorts with the same name may exist over time 
	if(result != null 
	   && sort instanceof GenericSort
	   && result.getSortDependingOn() != sort) {
	    result = new SortDependingFunction(template,
		    			       sort);
	    services.getNamespaces().functions().add(result);	    
	}

	if(result == null) {
	    result = new SortDependingFunction(template,
		    			       sort);
	    services.getNamespaces().functions().addSafely(result);
	}

        assert result.getSortDependingOn() == sort 
               : result + " depends on " + result.getSortDependingOn() 
                 + " (hash " + result.hashCode() + ")" 
                 + " but should depend on " + sort
                 + " (hash " + sort.hashCode() + ")";
        assert isSimilar(result) 
               : result + " should be similar to " + this;
        assert services.getNamespaces()
	                      .lookup(instantiateName(getKind(), 
	                	      		      sort)) == result;
	
	return result;	
    }
    
    
    public Sort getSortDependingOn() {
	return sortDependingOn;
    }


    public boolean isSimilar(SortDependingFunction p) {
	return getKind().equals(p.getKind());
    }

    
    public Name getKind() {
	return template.kind;
    }
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------     
    
    private static final class SortDependingFunctionTemplate {
	public final GenericSort sortDependingOn;
	public final Name kind;	
	public final Sort sort;
	public final ImmutableArray<Sort> argSorts;
	public final boolean unique;
	
	public SortDependingFunctionTemplate(GenericSort sortDependingOn,
		                             Name kind,
		                             Sort sort,
		                             ImmutableArray<Sort> argSorts,
		                             boolean unique) {
	    this.sortDependingOn = sortDependingOn;
	    this.kind = kind;
	    this.sort = sort;
	    this.argSorts = argSorts;
	    this.unique = unique;
	}
    }
}
