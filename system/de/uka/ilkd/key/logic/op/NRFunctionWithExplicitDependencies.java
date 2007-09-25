// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
/**
 * Created on 18.01.2005
 */
package de.uka.ilkd.key.logic.op;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

/**
 * Non Rigid Fucntion with explicit dependencies. This means a list of 
 * location of whose and only whose value the interpretation of the 
 * function symbol depends.
 * (May be generalized to more than locations in future)
 * 
 * The list of dependencies may be partitioned into several lists.
 */
public class NRFunctionWithExplicitDependencies extends NonRigidFunction {

    public static final char DEPENDENCY_LIST_STARTER = '[';
    public static final char DEPENDENCY_ELEMENT_SEPARATOR = ';';
    public static final char DEPENDENCY_LIST_SEPARATOR = '|';
    public static final char DEPENDENCY_LIST_END = ']';
    
    /**
     * Pseudo-location used to separate the partitions of the dependency list.
     * (this is necessary because currently all partitions are stored in a 
     * single ArrayOfLocation; when/if immutable lists of ArrayOfLocation 
     * become possible, one of these should be used instead)
     */
    private static final Location PARTITION_SEPARATOR 
            = new LocationVariable(new ProgramElementName(""), Sort.NULL);


    // HACK. Need more general framework for creating such functions see also
    // ArrayOp, AttributeOp
    // maps name -> mapDep2Op, where
    // mapDep2Op maps dependency-array -> op
    private static HashMap pool = new HashMap();
    
    /**
     * retrieves the non-rigid function with the given name and dependencies
     * or returns null if no such function symbol exists
     * @param name the Name of the function symbol to look for
     * @param dependencies the ArrayOfLocation with the dependencies
     * @return the non-rigid function symbol 
     */
    public static NRFunctionWithExplicitDependencies
	getSymbol(Name name, ArrayOfLocation dependencies) {
        HashMap mapDep2Op = (HashMap)pool.get(name);
        NRFunctionWithExplicitDependencies op = 
            (NRFunctionWithExplicitDependencies) mapDep2Op.get(dependencies);
        return op;
    }
    
    /**
     * retrieves the non-rigid function with the given name and dependencies
     * and creates one if not available
     * @param name the Name of the function symbol to look for
     * @param sort the Sort of the function symbol
     * @param argSorts the array of Sorts for the arguments
     * @param dependencies the array of Locations describing the dependencies
     * @return the non-rigid function symbol 
     */
    public static NRFunctionWithExplicitDependencies
        getSymbol(Name name, Sort sort, Sort[] argSorts, Location[] dependencies) {        
        return getSymbol(name, sort,
                new ArrayOfSort(argSorts), new ArrayOfLocation(dependencies));
    }
    
    /**
     * retrieves the non-rigid function with the given name and dependencies
     * and creates one if not available
     * @param name the Name of the function symbol to look for
     * @param sort the Sort of the function symbol
     * @param argSorts the ArrayOfSort for the arguments
     * @param depList partitioned dependencies as a list of ArrayOfLocation
     * @return the non-rigid function symbol 
     */
    public static NRFunctionWithExplicitDependencies
        getSymbol(Name name, Sort sort, ArrayOfSort argSorts,
                  List /*ArrayOfLocation*/ depList) {
        ListOfLocation deps = SLListOfLocation.EMPTY_LIST;
        Iterator it = depList.iterator();
        while(it.hasNext()) {
            ArrayOfLocation partition = (ArrayOfLocation) it.next();
            for(int i = 0; i < partition.size(); i++) {
                deps = deps.append(partition.getLocation(i));
            }
            if(it.hasNext()) {
                deps = deps.append(PARTITION_SEPARATOR);
            }
        }
        return getSymbol(name, 
                         sort, 
                         argSorts, 
                         new ArrayOfLocation(deps.toArray()));
    }
        
    /**
     * retrieves the non-rigid function with the given name and dependencies
     * and creates one if not available
     * @param name the Name of the function symbol to look for
     * @param sort the Sort of the function symbol
     * @param argSorts the ArrayOfSort for the arguments
     * @param dependencies the ArrayOfLocation with the dependencies
     * @return the non-rigid function symbol 
     */
    public static NRFunctionWithExplicitDependencies
        getSymbol(Name name, Sort sort, 
    	          ArrayOfSort argSorts, ArrayOfLocation dependencies) {

        HashMap mapDep2Op = (HashMap)pool.get(name);
        if (mapDep2Op == null) {
            mapDep2Op = new HashMap();
            pool.put(name, mapDep2Op);
        }
        NRFunctionWithExplicitDependencies op = 
            (NRFunctionWithExplicitDependencies) mapDep2Op.get(dependencies);
        
        if (op == null) {
            op = new NRFunctionWithExplicitDependencies
                (name, sort, argSorts, dependencies);
            mapDep2Op.put(name, op);
        }
                
        return op;
    }
        
    
    /**
     * the meaning of this function symbol depends on the values of the
     * locations contained in this array;
     */
    private final ArrayOfLocation dependencies;
    
    /**
     * the list of dependencies *without* markers for partition boundaries
     */
    private final ArrayOfLocation unpartitionedDependencies;

    /** the common name of the class of symbols */
    private final String classifier;
    
    /**
     * creates a non rigid function with given signaturen and dependencies
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the ArrayOfSort defining the argument sorts
     * @param dependencies the ArrayOfLocation whose values influence
     * the meaning of this symbol
     */
    private NRFunctionWithExplicitDependencies(Name name, Sort sort,
            ArrayOfSort argSorts, ArrayOfLocation dependencies) {
        super(name, sort, argSorts);
        this.dependencies = dependencies;
	this.classifier   = name.toString().substring
      (0, name.toString().indexOf(DEPENDENCY_LIST_STARTER));
        
        ListOfLocation unpartitionedDeps = SLListOfLocation.EMPTY_LIST;
        for(int i = 0; i < dependencies.size(); i++) {
            Location dep = dependencies.getLocation(i); 
            if(dep != PARTITION_SEPARATOR) {
                unpartitionedDeps = unpartitionedDeps.append(dep);
            }
        }
        unpartitionedDependencies 
                = new ArrayOfLocation(unpartitionedDeps.toArray());
    }

    public String classifier() {
	return classifier;
    }

    /**
     * two non-rigid function symbols can be matched if their list of
     * dependencies match 
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc, Services services) {
        MatchConditions result = mc;
        if (this == subst) return result;
        if (subst.getClass() != getClass()) {
            Debug.out("FAILED matching. Incomaptible operators " +
            "(template, operator)", this, subst);
            return null;
        }   
        
   
        final NRFunctionWithExplicitDependencies nrFunc = 
            (NRFunctionWithExplicitDependencies)subst;

        if (!(nrFunc.classifier.equals(classifier))) {
            Debug.out("Operator do not belong to the same category:", this, nrFunc);
            return null;
        }

        if (dependencies.size() == nrFunc.dependencies.size()) {
            for (int i = 0, locs = dependencies.size(); i<locs; i++) {
                result = dependencies.getLocation(i).
                match(nrFunc.dependencies.getLocation(i), result, services);
                if (result == null) { // fail fast
                    Debug.out
                    ("FAILED. NRFuncWithExplicitDependences mismatch " +
                            "(template, operator)", this, nrFunc);
                    return null;
                }
            }
            return result;
        }
        Debug.out("FAILED matching. NRWithExplicitDependencies match " +
                "failed because of incompatible locations (template, operator)", 
                this, subst);
        return null;
    }
    
    /**
     * returns an array of all locations this function depends on
     * @return the array of locations this function depends on
     */
    public ArrayOfLocation dependencies() {
        return unpartitionedDependencies;
    }
    
    public int getNumPartitions() {
        int result = 1;
        for(int i = 0; i < dependencies.size(); i++) {
            if(dependencies.getLocation(i) == PARTITION_SEPARATOR) {
                result++;
            }
        }
        return result;
    }

    /**
     * returns the i-th partition of the locations this function depends on
     */
    public ArrayOfLocation getDependencies(int i) {
        Debug.assertTrue(i >= 0);
        ListOfLocation result = SLListOfLocation.EMPTY_LIST;
        for(int j = 0; j < dependencies.size(); j++) {
            if(dependencies.getLocation(j) == PARTITION_SEPARATOR) {
                if(i == 0) {
                    break;
                } else {
                    i--;
                    continue;
                }
            }
            if(i == 0) {
                result = result.append(dependencies.getLocation(j));
            }
        }
        Debug.assertTrue(i == 0);
        return new ArrayOfLocation(result.toArray());
    }
    
    /**
     * toString
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(name().toString());
        sb.append(DEPENDENCY_LIST_STARTER);
        for (int i = 0; i<dependencies.size(); i++) {
            Location dep = dependencies.getLocation(i);
            if(dep == PARTITION_SEPARATOR) {
                sb.append(DEPENDENCY_LIST_SEPARATOR);
            } else {
                sb.append(dep);
                sb.append(DEPENDENCY_ELEMENT_SEPARATOR);
            }
        }
        sb.append(DEPENDENCY_LIST_END);
        sb.append("(");
        for (int i = 0; i<argSort().size(); i++) {
            sb.append(argSort().getSort(i));
            if (i<argSort().size()-1) {
                sb.append(",");
            }
        }
        sb.append("):");
        sb.append(sort());        
        return sb.toString();
    }
}
