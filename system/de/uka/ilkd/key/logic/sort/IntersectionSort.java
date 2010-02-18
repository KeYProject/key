// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/**
 * Created on 15.06.2005
 */
package de.uka.ilkd.key.logic.sort;

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.util.Debug;

/**
 * <p>
 * An intersection sort <code>I</code> is composed by exactly two sorts <code>S</code>, 
 * <code>T</code> and denotes their maximal subsort. This means, each sort being a subsort 
 * of both components extends (or is equal to) <code>I</code> as well.</p>
 * <p>
 * An intersection sort is always normalized during creation in order to keep consistent 
 * with the singleton property of sorts. That is to say that creation of the intersection 
 * sort (S,T) and (T,S), which denote obviously the same sort, returns the same sort object 
 * as they have the same normalform. </p> 
 * <p> The normalform is defined as follows:
 *    <ul> 
 *    <li><tt>(S1,S2)</tt>,
 *      where <tt>S1</tt> must be a simple (non-intersection) sort; for 
 *            <tt>S2</tt> there is no such restriction</li>           
 *    <li><tt>S1</tt> is no subsort of <tt>S2</tt> and vice versa, 
 *        i.e. intersection sorts are minimized</li>
 *    <li><tt>(S1,S2)</tt> are lexicographical ordered such that the name of <tt>S1</tt>
 *    is smaller than the name of sort <tt>S2</tt> (if <tt>S2</tt> is a simple sort) 
 *    or otherwise smaller than any sort being a composite of sort <tt>S2</tt></li>  
 *   </ul>  
 * If the normalform consists of exact one sort than the creation method of intersection 
 * sort returns the sort itself.</p>  
 * <p>An alternative definition of a normalform may use flattening, but 
 * would make matching of taclets more difficult. </p>
 */
public class IntersectionSort extends AbstractSort {

    /** 
     * performs a lookup in the sort namespace and returns the 
     * intersection sort of the given sorts. If none exists a new 
     * intersection sort is created and added to the namespace. 
     * The created intersection sort is in normalform. 
     *
     * @param sorts the SetOf<Sort> whose intersection sort has to be determined
     * @param services the Namespace with all known sorts to which if necessary 
     * the intersection sort of the given sorts is added
     * @return the intersection sort of the given sorts or null if this sort would have an empty domain 
     */
    public static Sort getIntersectionSort(ImmutableSet<Sort> sorts, Services services) {        
        return rightAssoc(sort(flatten(minimize(sorts.toArray(new Sort[sorts.size()])))), services);                     
    }
    
    /** 
     * performs a lookup in the sort namespace and returns the 
     * intersection sort of the given sorts. If none exists a new 
     * intersection sort is created and added to the namespace. 
     * The created intersection sort is in normalform. 
     *
     * @param components the SetOf<Sort> whose intersection sort has to be determined
     * @param sorts the Namespace with all known sorts to which if necessary 
     * the intersection sort of the given sorts is added
     * @param functions the Namespace where to add the sort depending functions 
     * @return the intersection sort of the given sorts or null if this sort would have an empty domain 
     */
    public static Sort getIntersectionSort(ImmutableSet<Sort> components, 
                                           Namespace sorts, Namespace functions) {        
        return rightAssoc(sort(flatten(minimize(components.toArray(new Sort[components.size()])))), 
        	sorts, functions);                     
    }
    
    /** 
     * performs a lookup in the sort namespace and returns the 
     * intersection sort of the given sorts. If none exists a new 
     * intersection sort is created and added to the namespace. 
     * The created intersection sort is in normalform. 
     *
     * @param s1 the first Sort 
     * @param s2 the second Sort
     * @param sorts the Namespace with all known sorts to which if necessary 
     * the intersection sort of the given sorts is added
     * @param functions the Namespace where to add sort depending functions like 
     * instance, casts etc.
     * @return the intersection sort of the given sorts or null if this sort would have an empty domain    
     */ 
    public static Sort getIntersectionSort(Sort s1, Sort s2, 
                                           Namespace sorts, 
                                           Namespace functions) {     
       
        Sort[] composites = flatten(minimize(new Sort[]{s1, s2}));
        
        if (composites.length == 1) {
            return composites[0];
        } else if (composites.length > 2) {
            return rightAssoc(composites, sorts, functions);
        }
        
        final Name sortName = createSortName(composites);                
        Sort result = (Sort) sorts.lookup(sortName);        
        if (result == null) {
            result = new IntersectionSort(sortName, 
                    composites[0], composites[1]);            
            if (((IntersectionSort)result).hasEmptyDomain(sorts)) {
                return null;
            }
            sorts.add(result);
            ((IntersectionSort)result).addDefinedSymbols(functions, sorts);
        }
        
        return result;        
    }
    
    /**
     * assumes all elements in <code>sorts</code> are non-intersection sorts
     * returns the intersection sort of the given sorts 
     * @param components
     * @return the intersection sort of the given sorts
     */
    private static Sort rightAssoc(Sort[] components, Services services) {      
        return rightAssoc(components, services.getNamespaces().sorts(), 
                          services.getNamespaces().functions());
    }   
    
    /**
     * assumes all elements in <code>sorts</code> are non-intersection sorts
     * returns the intersection sort of the given sorts 
     * @param components 
     * @return the intersection sort of the given sorts
     */
    private static Sort rightAssoc(Sort[] components, Namespace sorts, 
                                   Namespace functions) {      
        Sort result = components[components.length-1];
        for (int i = components.length - 2; i>=0; i--) {
            result = getIntersectionSort(components[i], result, sorts, functions);
        }
        return result;
    }   

    /**
     * creates the sort name for the composites. 
     * 
     * @param composites the array of Sort with the defining 
     * composite sorts of this intersection sort
     * @return the name of the intersection sort to be created
     */
    private static Name createSortName(Sort[] composites) {       
        final StringBuffer sortName = new StringBuffer("\\inter(");               
        
        for (int i = 0; i<composites.length; i++) {
            sortName.append(composites[i].name());
            if (i<composites.length - 1) {
                sortName.append(",");              
            } 
        }        
        sortName.append(")");
        
        return new Name(sortName.toString());
    }


    /** 
     * To become independant of the order of the constituents we
     * sort them in a lexicographical order. 
     * (assumes that different sorts have also different names). 
     * The used sorting algorithm is more or less a simple bubble sort
     * as we (hopely) have only to compute the intersection of some 
     * few sorts. 
     * @param sorts IList<Sort> the sorts to be sorted
     * @return return the same array but sorted in the lexicographical 
     * order of the sorts names
     */
    private static Sort[] sort(Sort[] sorts) {       
        if (sorts.length <= 1) return sorts;      
        Arrays.sort(sorts, 
                LexicographicalComparator.DEFAULT);
        return sorts;
    }

    /**
     * Removes all sorts of the given sorts that are a supersort 
     * of an existing one. For efficiency reasons flattening 
     * should be performed after minimizing.
     * @param sorts the SetOf<Sorts> to be minimized
     * @return the minimized array of sorts 
     */
    private static Sort[] minimize(Sort[] sorts) {                        
        final List minimized = 
            new LinkedList(Arrays.asList(sorts));
        
        // not optimized...
        for (int i = 0; i<sorts.length; i++) {
            final Sort s1 = sorts[i];          
            for (int j = i+1; j<sorts.length; j++) {                
                final Sort s2 = sorts[j];                
                if (s2.extendsTrans(s1)) {
                    minimized.remove(s1);
                    break;
                } else if (s1.extendsTrans(s2)) {
                    minimized.remove(s2);                   
                }
            }
        }
        return (Sort[]) minimized.toArray(new Sort[minimized.size()]);
    }


    /**
     * flattens the given sorts by decomposing intersection 
     * sorts
     * @param sorts the IList<Sort> to be flattened
     * @return the flattened list of sorts 
     * (i.e. means without subsorts)  
     */
    private static Sort[] flatten(Sort[] sorts) {
        List result = new LinkedList();
        for (Sort sort : sorts) {
            if (!(sort instanceof IntersectionSort)) {
                result.add(sort);
            } else {
                final IntersectionSort sortsIntersect = (IntersectionSort) sort;
                result.addAll(Arrays.asList
                        (flatten(sortsIntersect.compositesAsArray())));
            }
        }
        return (Sort[]) result.toArray(new Sort[result.size()]);
    }

    /**
     * returns the composites as array
     * @return the composites as array
     */
    private Sort[] compositesAsArray() {        
        return new Sort []{leftComposite, rightComposite};
    }

    /** 
     * left composite of this intersection sort. Has to be a simple sort, 
     * i.e. non composite sort
     */
    private final Sort leftComposite;
    /** 
     * left composite of this intersection sort 
     * (may be simple or intersection sort)
     */
    private final Sort rightComposite;
    
    /** the non-intersection sorts this sort inherits of */
    private ImmutableSet<Sort> extendsSorts = null;

    /** 
     * empty domain caches the computation if the domain of
     * this intersection sort is empty 
     */
    private boolean emptyDomainComputed;
    private boolean emptyDomain;   

    /** 
     * creates an intersection sort of the given name consisting of the 
     * given composite sorts. Does not perform any normalisation. 
     * @param name the Name of the intersection sort
     * @param leftComposite the Sort to be intersected with  
     *   <code>rightComposite</code> and is must not be 
     *   of type intersection sort
     * @param rightComposite an arbitrary Sort being intersected with 
     * <code>leftComposite</code> 
     */
    private IntersectionSort(Name name, 
                             Sort leftComposite, 
                             Sort rightComposite) {
        super(name);
        this.leftComposite  = leftComposite;
        Debug.assertFalse(leftComposite instanceof IntersectionSort);
        this.rightComposite = rightComposite; 
        
    }

    /** 
     * return the set of the 'real' sorts this 
     * intersection sort consists of (no intersection sorts) 
     */
    public ImmutableSet<Sort> extendsSorts() {    
        if (extendsSorts == null) {
            extendsSorts = DefaultImmutableSet.<Sort>nil().add(leftComposite);
            if (rightComposite instanceof IntersectionSort) {
                extendsSorts = extendsSorts.
                union(rightComposite.extendsSorts());
            } else {
                extendsSorts = extendsSorts.add(rightComposite);
            }
            extendsSorts = asSet(minimize(extendsSorts.toArray(new Sort[extendsSorts.size()])));            
        }
        return extendsSorts;
    }

    /**
     * returns the <code>i</code>-th component of this intersection sort 
     * (where 0 is left component and 1 is the right component)
     * 
     * @return the <code>i</code>-th component of this intersection sort
     * @throws IndexOutOfBoundsException if <code>i</code> is greater than 1
     */
    public Sort getComponent(int i) {      
        if (i<0 || i>1)  {
            throw new IndexOutOfBoundsException(i + " is out of bound.");
        }
        return i==0 ? leftComposite : rightComposite;
    }
        
    /**
     * returns the number of composites (always two)
     */
    public int memberCount() {
        return 2;
    }
    
    
    /**
     * returns true iff the given sort is a transitive supersort of this sort
     * or it is the same.
     */
    public boolean extendsTrans(Sort p_sort) {      
       if (p_sort == this || p_sort == Sort.ANY) return true; 
       
       boolean extendsTrans = true;
       
       /**
        * for all s\in sort.composites 
        *       exists c\in this.composites
        *          c.extendsTrans(s)
        */
        if (p_sort instanceof IntersectionSort) {            
            final IntersectionSort p_intersect = ((IntersectionSort)p_sort); 
            for (int i = 0, mc = p_intersect.memberCount(); i<mc; i++) {
                final Sort p_composite = p_intersect.getComponent(i);                                  
                extendsTrans = extendsTrans &&
                    this.extendsTransHelp(p_composite);
                if (!extendsTrans) break; 
            }
        } else {
            extendsTrans = extendsTransHelp(p_sort) ;
        }
       
        return extendsTrans;
    }

    /**
     * tests if one of the composites is a subsort (or equal) of the given one
     * @param sort the Sort to test to be a supersort (or equal) of one of the 
     * composites
     * @return true if sort is a supersort of one of the composites (inclusive equal to)
     */
    private boolean extendsTransHelp(Sort sort) {
        for (int i = 0, sz=memberCount(); i<sz; i++) {
            if (getComponent(i).extendsTrans(sort)) {
                return true;
            }
        }
        return false;
    }
    
    /**
     * returns true if the represented domain is empty. If you consider other logics 
     * than JavaCardDL you will most probably have to subclass IntersectionSort and
     * overwrite this method. 
     * @return true if other than reference types, which are siblings in the type hierarchy, 
     * intersect    
     */
    private boolean hasEmptyDomain(Namespace sorts) {       
       if (emptyDomainComputed) return emptyDomain;                     

       emptyDomain = true;

       for (final Named n : sorts.allElements()) {
           final Sort s = (Sort) n;
                  
           if (s != this) {
               if (s instanceof IntersectionSort && 
                       ((IntersectionSort)s).hasEmptyDomain(sorts)) {
                   continue;
               } else if (extendsTransAll(s)) {
                   emptyDomain = false;
                   break;
               }           
           }    
       }

       emptyDomainComputed = true;
       return emptyDomain;
    }
    
    /**
     * checks if s extends all composite sorts
     * @param s Sort to be checked
     * @return true iff s extends all composites of this intersection sort
     */
    private boolean extendsTransAll(Sort s) {
        for (int i = 0; i<memberCount(); i++) {
            if (!s.extendsTrans(getComponent(i))) {
                return false;
            }
        }
        return true;
    }

    /** 
     * toString 
     */
    public String toString() {
        return name().toString();
    }
    
    // helper
    /**
     * converts the given array of sorts into a set
     */
    private static ImmutableSet<Sort> asSet(Sort[] s) {
        ImmutableSet<Sort> set = DefaultImmutableSet.<Sort>nil();
        for (Sort value : s) {
            set = set.add(value);
        }
        return set;
    }

        
    // Some comparators used for determining the minimal supersort to be created
    
    /**
     * compares to sorts using the canonical lexicographical order on their names
     */
    private final static class LexicographicalComparator implements Comparator {

        public static final LexicographicalComparator DEFAULT = 
            new LexicographicalComparator();

        public int compare(Object o1, Object o2) {
            final Sort s1 = (Sort)o1;
            final Sort s2 = (Sort)o2;
            return s1.name().toString().compareTo(s2.name().toString());
        }               
    }

         
}
