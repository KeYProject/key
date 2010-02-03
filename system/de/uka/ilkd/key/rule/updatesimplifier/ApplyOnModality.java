// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/*
 * Created on 16.12.2004
 */
package de.uka.ilkd.key.rule.updatesimplifier;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.LRUCache;

/**
 * This simplification rule merges two updates and (optional) 
 * some assignment pairs with no influence on the fromula 
 * are removed
 */
public class ApplyOnModality extends AbstractUpdateRule {

    /** marker that all program variables have to be protected */
    private final static Object PROTECT_ALL = new Object(); 

    /** marker that all heap locations have to be protected */
    private final static Object PROTECT_HEAP = new Object(); 
    
    private boolean deletionEnabled;

    private static LRUCache<Term, HashSet<Object>> protectedVarsCache = 
        new LRUCache<Term, HashSet<Object>>(1000);
    
    /**
     * @param updateSimplifier
     * @param deletionEnabled a boolean flag indictaing if effectless
     * updates shall be deleted
     */
    public ApplyOnModality(UpdateSimplifier updateSimplifier, 
            boolean deletionEnabled) {
        super(updateSimplifier);   
        this.deletionEnabled = deletionEnabled;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.IUpdateRule#isApplicable(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public boolean isApplicable(Update update, Term target) {                
        return target.op() instanceof Modality;         
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.rule.IUpdateRule#apply(de.uka.ilkd.key.rule.updatesimplifier.Update,
     *      de.uka.ilkd.key.logic.Term)
     */
    public Term apply(Update update, Term target, Services services) {

        final ArrayOfAssignmentPair pairs = deletionEnabled ? new ArrayOfAssignmentPair(
                remove(update, target, services))
        : update.getAllAssignmentPairs();
  
        return pairs.size() == 0   ? target : UpdateSimplifierTermFactory.DEFAULT
                        .createUpdateTerm(pairs, target);   
    }

    /**
     * removes assignmentpairs updating locations which are not 
     * used in the tail of the formula
     * @author bubel         
     */
    public AssignmentPair[] remove(Update up, Term target, Services services) {
        final ArrayOfAssignmentPair pairs = up.getAllAssignmentPairs();        
        final HashSet<Object> protectedProgVars = collectProgramVariables(target, services);
        final List<AssignmentPair> result = new ArrayList<AssignmentPair>(pairs.size());

        for (int i = 0, size=pairs.size(); i<size; i++) {
            final AssignmentPair pair =  pairs.getAssignmentPair(i);            
            final Location loc = pair.location();
                       
            if ( protectedLocation ( loc, protectedProgVars ) )
                result.add ( pair );
        }    
        return result.toArray(new AssignmentPair[result.size()]);
    }
    
    /**
     * looks up if the given location is protected, i.e. must not be deleted
     * @param loc the Location to check
     * @param protectedProgVars
     * @return true if the given location is protected
     */
    private boolean protectedLocation(Location loc, 
            HashSet<? extends Object> protectedProgVars) {
        // currently it would be safe to comment the PROTECTED_HEAP part out as 
        // heap locations are generally not thrown away. But in principle one can think
        // of a more finegrained control
        return protectedProgVars.contains(PROTECT_ALL) ||
              (protectedProgVars.contains(PROTECT_HEAP) && isHeapLocation(loc)) || 
              (isHeapLocation(loc) || protectedProgVars.contains(loc) ||
	    loc.name().equals(new ProgramElementName("<transactionCounter>")));
    }

    
    /**
     * returns true if the location is a heap location, i.e. a static or instance field or
     * an array operator
     * @param loc the Location to test
     * @return true iff the location denotes a heap location
     */
    private boolean isHeapLocation(Location loc) {        
        return (!(loc instanceof ProgramVariable) || ((ProgramVariable)loc).isMember())
               && !(loc instanceof NonRigidFunctionLocation);
    }

    /**
     * collects all local program variables
     * @param target
     * @return the HashSet containing all protected locations and the special protection markers
     * {@link #PROTECT_ALL} and {@link #PROTECT_HEAP}
     */
    private HashSet<Object> collectProgramVariables(Term target, Services services) {
        if (protectedVarsCache.containsKey(target)) {           
            return protectedVarsCache.get(target); 
        }
        HashSet<Object> foundProgVars = new HashSet<Object>();
        
        final Operator targetOp = target.op();
        
        if (targetOp instanceof ProgramVariable
            || targetOp instanceof NonRigidFunctionLocation) {
            foundProgVars.add(targetOp);
        } else if (targetOp instanceof NonRigidHeapDependentFunction) {
            foundProgVars.add(PROTECT_HEAP);
        } else if (targetOp instanceof NonRigidFunction && 
                   !(targetOp instanceof ProgramMethod)) {
            foundProgVars.add(PROTECT_ALL);
            return foundProgVars;
        }
        
        if (target.javaBlock() != JavaBlock.EMPTY_JAVABLOCK) {
            ProgramVariableCollector pvc = 
                new ProgramVariableCollector(target.javaBlock().program(), 
                                             services,
                                             true);
            pvc.start();
            foundProgVars.addAll(pvc.result());
        }
        
        for (int i = 0; i<target.arity(); i++) {
            foundProgVars.addAll(collectProgramVariables(target.sub(i), 
                                                         services));
        }
        
        protectedVarsCache.put(target, foundProgVars);
        return foundProgVars;
    }      
    
    public Term matchingCondition (Update update, 
	    		           Term target, 
	    		           Services services) {
        // a modality is not a location
        assert false : "matchingCondition(...) must not be called for target " + target;
        return null; // unreachable
    }
}
