// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the LoopInvariant interface.
 */
public class LoopInvariantImpl implements LoopInvariant {

    private final LoopStatement loop;
    private final Term originalInvariant;
    private final SetOfTerm originalPredicates;
    private final SetOfLocationDescriptor originalModifies;
    private final Term originalVariant;
    private final ParsableVariable originalSelfVar;
    private final Map /*Operator (normal) -> Function (atPre)*/ 
                                                        originalAtPreFunctions;
    private final boolean predicateHeuristicsAllowed;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    /**
     * Creates a loop invariant.
     * @param loop the loop to which the invariant belongs
     * @param invariant the invariant formula
     * @param predicates the loop predicates
     * @param modifies the modifier set
     * @param variant the variant term
     * @param selfVar the variable used for the receiver object
     * @param atPreFunctions the functions used for atPre
     * @param predicateHeuristicsAllowed whether heuristics for generating
     *        additional loop predicates are allowed
     */
    public LoopInvariantImpl(LoopStatement loop,
                             Term invariant,
                             SetOfTerm predicates,
                             SetOfLocationDescriptor modifies,  
                             Term variant, 
                             ParsableVariable selfVar,
                             /*inout*/ Map /*Operator (normal) 
                             -> Function (atPre)*/ atPreFunctions,
                             boolean predicateHeuristicsAllowed) {
        assert loop != null;
        assert predicates != null;
        assert modifies != null;
        assert atPreFunctions != null;
        this.loop                       = loop;
	this.originalInvariant          = invariant;
        this.originalPredicates         = predicates;
        this.originalVariant            = variant;
        this.originalModifies           = modifies;
        this.originalSelfVar            = selfVar;   
        this.predicateHeuristicsAllowed = predicateHeuristicsAllowed;
        this.originalAtPreFunctions     = new LinkedHashMap();
        this.originalAtPreFunctions.putAll(atPreFunctions);
    }
    
    
    /**
     * Creates an empty, default loop invariant for the passed loop.
     */
    public LoopInvariantImpl(LoopStatement loop, ParsableVariable selfVar) {
        this(loop, 
             null, 
             SetAsListOfTerm.EMPTY_SET, 
             SetAsListOfLocationDescriptor.EMPTY_SET, 
             null, 
             selfVar,
             new LinkedHashMap(),
             true);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Term -> Term*/ getReplaceMap(Term selfTerm) {
        Map result = new LinkedHashMap();
        
        //self
        if(selfTerm != null) {
            assert originalSelfVar.sort().equals(selfTerm.sort());
            result.put(TermBuilder.DF.var(originalSelfVar), selfTerm);
        }
        
        //-parameters and other local variables are always kept up to
        // date by the ProgVarReplaceVisitor
        //-atPre-functions are kept up to date by the IntroAtPreDefinitionsOp
        
        return result;
    }
    
    
    private Map /*Term -> Term*/ getInverseReplaceMap(Term selfTerm) {
       Map result = new LinkedHashMap();
       Map replaceMap = getReplaceMap(selfTerm);
       Iterator it = replaceMap.entrySet().iterator();
       while(it.hasNext()) {
           Map.Entry entry = (Map.Entry) it.next();
           result.put(entry.getValue(), entry.getKey());
       }
       return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public LoopStatement getLoop() {
        return loop;
    }

    
    public Term getInvariant(Term selfTerm) {
        assert (selfTerm == null) == (originalSelfVar == null);
        Map replaceMap = getReplaceMap(selfTerm);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalInvariant);
    }
    
    
    public SetOfTerm getPredicates(Term selfTerm) {
        assert (selfTerm == null) == (originalSelfVar == null);
        Map replaceMap = getReplaceMap(selfTerm);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalPredicates);
    }

    
    public SetOfLocationDescriptor getModifies(Term selfTerm) {
        assert (selfTerm == null) == (originalSelfVar == null);
        Map replaceMap = getReplaceMap(selfTerm);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalModifies);
    }
    

    public Term getVariant(Term selfTerm) {
        assert (selfTerm == null) == (originalSelfVar == null);
        Map replaceMap = getReplaceMap(selfTerm);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalVariant);
    }
    
    
    public boolean getPredicateHeuristicsAllowed() {
        return predicateHeuristicsAllowed;
    }
    
    
    
    public ParsableVariable getSelfVar() {
        return originalSelfVar;
    }
    
    
    public /*inout*/ Map /*Operator (normal) 
                           -> Function (atPre)*/ getAtPreFunctions() {
        Map result = new LinkedHashMap();
        result.putAll(originalAtPreFunctions);
        return result;
    }
    
    
    public LoopInvariant setLoop(LoopStatement loop) {
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     originalPredicates,
                                     originalModifies,
                                     originalVariant,
                                     originalSelfVar,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    
    
    public LoopInvariant setInvariant(Term invariant, Term selfTerm) {
        assert (selfTerm == null) == (originalSelfVar == null);
        Map inverseReplaceMap = getInverseReplaceMap(selfTerm);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        return new LoopInvariantImpl(loop, 
                                     or.replace(invariant), 
                                     originalPredicates,  
                                     originalModifies, 
                                     originalVariant, 
                                     originalSelfVar,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    

    public LoopInvariant setPredicates(SetOfTerm predicates, Term selfTerm) {
        assert (selfTerm == null) == (originalSelfVar == null);
        Map inverseReplaceMap = getInverseReplaceMap(selfTerm);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     or.replace(predicates),
                                     originalModifies,
                                     originalVariant,
                                     originalSelfVar,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    
    
    public LoopInvariant setPredicateHeuristicsAllowed(
                                        boolean predicateHeuristicsAllowed) {
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     originalPredicates,
                                     originalModifies,
                                     originalVariant,
                                     originalSelfVar,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    
    
    public void visit(Visitor v) {
        v.performActionOnLoopInvariant(this);
    }
    
    
    public String toString() {
        return "invariant: " 
                + originalInvariant 
                + "; predicates: " 
                + originalPredicates 
                + "; modifies: " 
                + originalModifies
                + "; variant: "
                + originalVariant;
    }
}
