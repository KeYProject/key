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

package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.pp.LogicPrinter;

/**
 * Standard implementation of the LoopInvariant interface.
 */
public final class LoopInvariantImpl implements LoopInvariant {

    private final LoopStatement loop;
    private final IProgramMethod pm;
    private final KeYJavaType kjt;
    private final Map<LocationVariable,Term> originalInvariants;
    private final Map<LocationVariable,Term> originalModifies;
    private final Map<LocationVariable,
                      ImmutableList<InfFlowSpec>> originalInfFlowSpecs;
    private final Term originalVariant;
    private final Term originalSelfTerm;
    private final ImmutableList<Term> localIns;
    private final ImmutableList<Term> localOuts;
    private final Map<LocationVariable,Term> originalAtPres;
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    /**
     * Creates a loop invariant.
     * @param loop the loop to which the invariant belongs
     * @param invariant the invariant formula
     * @param modifies the modifier set
     * @param infFlowSpecs low variables for information flow
     * @param variant the variant term
     * @param selfTerm the term used for the receiver object
     * @param heapAtPre the term used for the at pre heap
     */
    public LoopInvariantImpl(LoopStatement loop,
                             IProgramMethod pm,
                             KeYJavaType kjt,
                             Map<LocationVariable, Term> invariants,
                             Map<LocationVariable, Term> modifies,
                             Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs,
                             Term variant,
                             Term selfTerm,
                             ImmutableList<Term> localIns,
                             ImmutableList<Term> localOuts,
                             Map<LocationVariable, Term> atPres) {
        assert loop != null;
        //assert modifies != null;
        //assert heapAtPre != null;
        this.loop                       = loop;
        this.pm                         = pm;
        this.kjt                        = kjt;
        this.originalInvariants         =
                invariants == null ? new LinkedHashMap<LocationVariable,Term>() : invariants;
        this.originalVariant            = variant;
        this.originalModifies           =
                modifies == null ? new LinkedHashMap<LocationVariable,Term>() : modifies;
        this.originalInfFlowSpecs       =
                infFlowSpecs == null ? new LinkedHashMap<LocationVariable,
                                                         ImmutableList<InfFlowSpec>>()
                                     : infFlowSpecs;
        this.originalSelfTerm           = selfTerm;
        this.localIns                   = localIns;
        this.localOuts                  = localOuts;
        this.originalAtPres             =
                atPres == null ? new LinkedHashMap<LocationVariable,Term>() : atPres;
    }


    /**
     * Creates an empty, default loop invariant for the passed loop.
     */
    public LoopInvariantImpl(LoopStatement loop,
                             IProgramMethod pm,
                             KeYJavaType kjt,
	    		     Term selfTerm, 
	    		     Map<LocationVariable,Term> atPres) {
        this(loop, pm, kjt, null, null, null, null, selfTerm, null, null, atPres);
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator, Operator, Term -> Term*/<Term, Term> getReplaceMap(
            Term selfTerm,
            Map<LocationVariable,Term> atPres,
            Services services) {
        final Map<Term, Term> result = new LinkedHashMap<Term, Term>();
        
        //self
        if(selfTerm != null) {
//            assert selfTerm.sort().extendsTrans(originalSelfTerm.sort()) :
//        	   "instantiating sort " + originalSelfTerm.sort()
//        	   + " with sort " + selfTerm.sort()
//        	   + " which is not a subsort!";
            result.put(originalSelfTerm, selfTerm);
        }
        
        //-parameters and other local variables are always kept up to
        // date by the ProgVarReplaceVisitor

        if(atPres != null) {
          for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps(services)) {
             if(atPres.get(h) != null && originalAtPres.get(h) != null) {
                 assert originalAtPres.get(h).sort().equals(atPres.get(h).sort());
                 result.put(originalAtPres.get(h), atPres.get(h));
             }
          }
        }

        return result;
    }
    
    
    private Map<Term,Term> getInverseReplaceMap(Term selfTerm,
                                                Map<LocationVariable,Term> atPres,
                                                Services services) {
       final Map<Term,Term> result = new LinkedHashMap<Term,Term>();
       final Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
       for(Map.Entry<Term, Term> next: replaceMap.entrySet()) {
           result.put(next.getValue(), next.getKey());
       }
       return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public LoopStatement getLoop() {
        return loop;
    }

    @Override    
    public Term getInvariant(LocationVariable heap,
                             Term selfTerm,
            		     Map<LocationVariable,Term> atPres,
            		     Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalInvariants.get(heap));
    }
    
    @Override
    public Term getInvariant(Term selfTerm, Map<LocationVariable,Term> atPres, Services services){
        assert (selfTerm == null) == (originalSelfTerm == null);
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalModifies.get(baseHeap));
    }
    
    @Override
    public Term getInvariant(Services services) {
        return originalInvariants.get(services.getTypeConverter().getHeapLDT().getHeap());
    }
    
    @Override
    public Term getModifies(LocationVariable heap, Term selfTerm,
            		    Map<LocationVariable,Term> atPres,
            		    Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalModifies.get(heap));
    }
    
    @Override
    public Term getModifies(Term selfTerm, Map<LocationVariable,Term> atPres, Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalModifies.get(baseHeap));
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap,
                                                      Term selfTerm,
                                                      Map<LocationVariable, Term> atPres,
                                                      Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replaceInfFlowSpec(originalInfFlowSpecs.get(heap));
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap) {
        return originalInfFlowSpecs.get(heap);
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services) {
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        return getInfFlowSpecs(baseHeap);
    }

    @Override
    public Term getVariant(Term selfTerm, 
            		   Map<LocationVariable,Term> atPres,
            		   Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalVariant);
    }

    @Override
    public Map<LocationVariable,Term> getInternalInvariants() {
        return originalInvariants;
    }

    @Override
    public Term getInternalVariant() {
        return originalVariant;
    }

    @Override
    public Map<LocationVariable,Term> getInternalModifies(){
    	return originalModifies;
    }
    
    @Override
    public Map<LocationVariable,
               ImmutableList<InfFlowSpec>> getInternalInfFlowSpec(){
        return originalInfFlowSpecs;
    }
    
    @Override
    public Term getInternalSelfTerm() {
        return originalSelfTerm;
    }

    @Override
    public Term getModifies() {
        return originalModifies.values().iterator().next();
    }
    
    @Override
    public Map<LocationVariable,Term> getInternalAtPres() {
        Map<LocationVariable,Term> result = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable h : originalAtPres.keySet()) {
          result.put(h, originalAtPres.get(h));
        }
        return result;
    }

    @Override
    public LoopInvariant create(LoopStatement loop,
                                IProgramMethod pm,
                                KeYJavaType kjt,
                                Map<LocationVariable,Term> invariants,
                                Map<LocationVariable,Term> modifies,
                                Map<LocationVariable,
                                    ImmutableList<InfFlowSpec>> infFlowSpecs,
                                Term variant,
                                Term selfTerm,
                                ImmutableList<Term> localIns,
                                ImmutableList<Term> localOuts,
                                Map<LocationVariable,Term> atPres) {
        return new LoopInvariantImpl(loop, pm, kjt, invariants,
                                     modifies, infFlowSpecs, variant, selfTerm,
                                     localIns, localOuts, atPres);
    }

    @Override
    public LoopInvariant create(LoopStatement loop,
                                Map<LocationVariable,Term> invariants,
                                Map<LocationVariable,Term> modifies,
                                Map<LocationVariable,
                                    ImmutableList<InfFlowSpec>> infFlowSpecs,
                                Term variant,
                                Term selfTerm,
                                ImmutableList<Term> localIns,
                                ImmutableList<Term> localOuts,
                                Map<LocationVariable,Term> atPres) {
        return create(loop, pm, kjt, invariants, modifies, infFlowSpecs,
                      variant, selfTerm, localIns, localOuts, atPres);
    }

    @Override
    public LoopInvariant instantiate(Map<LocationVariable,Term> invariants,
                                     Term variant) {
        return configurate(invariants, originalModifies, originalInfFlowSpecs, variant);
    }

    @Override
    public LoopInvariant configurate(Map<LocationVariable,Term> invariants,
                                     Map<LocationVariable,Term> modifies,
                                     Map<LocationVariable,
                                         ImmutableList<InfFlowSpec>> infFlowSpecs,
                                     Term variant) {
        return create(loop, invariants, modifies, infFlowSpecs, variant,
                      originalSelfTerm, localIns, localOuts, originalAtPres);
    }

    @Override
    public LoopInvariant setLoop(LoopStatement loop) {
        return new LoopInvariantImpl(loop,
                                     pm,
                                     kjt,
                                     originalInvariants,
                                     originalModifies,
                                     originalInfFlowSpecs,
                                     originalVariant,
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }

    @Override
    public LoopInvariant setTarget(IProgramMethod newPM) {
        return new LoopInvariantImpl(loop,
                                     newPM,
                                     kjt,
                                     originalInvariants,
                                     originalModifies,
                                     originalInfFlowSpecs,
                                     originalVariant, 
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }

    @Override
    public LoopInvariant setInvariant(Map<LocationVariable,Term> invariants, 
            			      Term selfTerm,
            			      Map<LocationVariable,Term> atPres,
            			      Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap, services.getTermFactory());
        Map<LocationVariable,Term> newInvariants = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : invariants.keySet()) {
           newInvariants.put(heap, or.replace(invariants.get(heap)));
        }
        return new LoopInvariantImpl(loop,
                                     pm,
                                     kjt,
                                     newInvariants,
                                     originalModifies,
                                     originalInfFlowSpecs,
                                     originalVariant,
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }
    
    
    @Override
    public void visit(Visitor v) {
        v.performActionOnLoopInvariant(this);
    }
    
    @Override
    public String toString() {
        return "invariants: " 
                + originalInvariants
                + "; modifies: " 
                + originalModifies
                + "; information flow specification: "
                + originalInfFlowSpecs
                + "; variant: "
                + originalVariant
                + "; input parameters: " 
                + localIns
                + "; output parameters: " 
                + localOuts;
    }

    @Override
    public String getPlainText(Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
       final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
       final LocationVariable baseHeap = heapLDT.getHeap();
       
       String mods = "";
       for (LocationVariable h : heapLDT.getAllHeaps(services)) {
           if (originalModifies.get(h) != null) {
               String printMods = LogicPrinter.quickPrintTerm(originalModifies.get(h), services, usePrettyPrinting, useUnicodeSymbols);
               mods = mods
                       + "\n"
                       + "mod"
                       + (h == baseHeap ? "" : "[" + h + "]")
                       + ": "
                       + printMods.trim();
           }
       }
       
       String invariants = "";
       for (LocationVariable h : heapLDT.getAllHeaps(services)) {
           if (originalInvariants.get(h) != null) {
               String printPosts = LogicPrinter.quickPrintTerm(originalInvariants.get(h), services, usePrettyPrinting, useUnicodeSymbols);
               invariants = invariants
                       + "\n"
                       + "invariant"
                       + (h == baseHeap ? "" : "[" + h + "]")
                       + ": "
                       + printPosts.trim();
           }
       }
       
       return invariants
             + ";\nvariant: "
             + LogicPrinter.quickPrintTerm(originalVariant, services, usePrettyPrinting, useUnicodeSymbols).trim() +
             mods;
    }


    @Override
    public String getDisplayName() {
	return "Loop Invariant";
    }


    public IProgramMethod getTarget() {
        return this.pm;
    }


    @Override
    public KeYJavaType getKJT() {
	return this.kjt;
    }

    @Override
    public String getName() {
        return "Loop Invariant";
    }

    @Override
    public String getUniqueName() {
        if (pm != null)
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + getTarget().getUniqueName();
        else
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + Math.abs(getLoop().hashCode());
    }

    @Override
    public VisibilityModifier getVisibility() {
	assert false;
	return null;
    }

    @Override
    public boolean hasInfFlowSpec(Services services) {
        return !getInfFlowSpecs(services).isEmpty();
    }

    public LoopInvariant setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new LoopInvariantImpl(loop, (IProgramMethod)newPM, newKJT,
                                     originalInvariants, originalModifies,
                                     originalInfFlowSpecs, originalVariant,
                                     originalSelfTerm, localIns, localOuts,
                                     originalAtPres);
    }


    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, ProgramVariable> atPreVars =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        for (LocationVariable h: originalAtPres.keySet()) {
            atPreVars.put(h, (ProgramVariable)originalAtPres.get(h).op());
        }
        final ProgramVariable self;
        if(this.originalSelfTerm != null
                && this.originalSelfTerm.op() instanceof ProgramVariable) {
            self = (ProgramVariable)this.originalSelfTerm.op();
        } else if (this.originalSelfTerm != null) {
            self = new LocationVariable(
                    new ProgramElementName(originalSelfTerm.op().toString()), kjt);
        } else {
            self = null;
        }
        return new OriginalVariables(self, null, null, atPreVars,
                                     ImmutableSLList.<ProgramVariable>nil());
    }
}
