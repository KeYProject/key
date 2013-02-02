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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SortException;
import de.uka.ilkd.key.util.Debug;


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
	      template.unique);
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
    
    

    /**
     * tries to match sort <code>s1</code> to fit sort <code>s2</code>
     * @param s1 Sort tried to matched (maybe concrete or (contain) generic)
     * @param s2 concrete Sort 
     * @param mc the MatchConditions up to now
     * @return <code>null</code> if failed the resulting match conditions 
     * otherwise 
     */
    private static MatchConditions matchSorts(Sort s1, 
	    			              Sort s2, 
	    			              MatchConditions mc,
	    			              Services services) {
        assert !(s2 instanceof GenericSort)
               : "Sort s2 is not allowed to be of type generic.";
        if (!(s1 instanceof GenericSort)) {
            if (s1 == s2) {
                return mc;
            } else {
                Debug.out("FAIL. Sorts not identical.", s1, s2);
                return null;
            }
        } else {        
            final GenericSort gs = (GenericSort)s1;
            final GenericSortCondition c 
            	= GenericSortCondition.createIdentityCondition(gs, s2);                                               
            if(c == null) {
                Debug.out("FAILED. Generic sort condition");
                return null;
            } else {
                try {                   
                    mc = mc.setInstantiations(mc.getInstantiations()
                	                        .add(c, services));
                } catch(SortException e) {
                    Debug.out("FAILED. Sort mismatch.", s1, s2);
                    return null;
                }
            }                  
        }               
        return mc;
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
	    					         Services services) {
	return (SortDependingFunction) 
			services.getNamespaces()
			        .functions()
	                        .lookup(instantiateName(kind, Sort.ANY));
    }
        

    public SortDependingFunction getInstanceFor(Sort sort, 
	    				        Services services) {
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


    
    /**
     * Taking this sortdepending function as template to be matched against <code>op</code>, 
     * the necessary conditions are returned or null if not unifiable (matchable).
     * A sortdepending function is matched successfully against another sortdepending function
     * if the sorts can be matched and they are of same kind.      
     */
    @Override    
    public MatchConditions match(SVSubstitute subst, 
                                 MatchConditions mc,
                                 Services services) {  
        if(!(subst instanceof SortDependingFunction)) {
            Debug.out("FAILED. Given operator cannot be matched by a sort" +
            		"depending function (template, orig)", this, subst);
            return null;
        }

        final SortDependingFunction sdp = (SortDependingFunction)subst;   
        if(!isSimilar(sdp)) {
            Debug.out("FAILED. Sort depending symbols not similar.", this, subst);            
            return null;
        }
        
        final MatchConditions result =  matchSorts(getSortDependingOn(), 
        		      	                   sdp.getSortDependingOn(), 
        		      	                   mc,
        		      	                   services);        
        if (result == null) {
            Debug.out("FAILED. Depending sorts not unifiable.", this, subst);
            return null;
        }
        
        return result;        
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
