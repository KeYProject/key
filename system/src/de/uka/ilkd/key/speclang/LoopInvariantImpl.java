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


package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.util.Triple;

/**
 * Standard implementation of the LoopInvariant interface.
 */
public final class LoopInvariantImpl implements LoopInvariant {

    private final LoopStatement loop;
    private final IProgramMethod pm;
    private final ExecutionContext innermostExecCont;
    private Term guard;
    private final Map<LocationVariable,Term> originalInvariants;
    private final Map<LocationVariable,Term> originalModifies;
    private Map<LocationVariable,
                ImmutableList<Triple<ImmutableList<Term>,
                                     ImmutableList<Term>,
                                     ImmutableList<Term>>>> originalRespects;
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
     * @param respects low variables for information flow
     * @param variant the variant term
     * @param selfTerm the term used for the receiver object
     * @param heapAtPre the term used for the at pre heap
     */
    public LoopInvariantImpl(LoopStatement loop,
                             IProgramMethod pm,
                             ExecutionContext innermostExecCont,
                             Map<LocationVariable,Term> invariants,
                             Map<LocationVariable,Term> modifies,
                             Map<LocationVariable,
                             ImmutableList<Triple<ImmutableList<Term>,
                                                  ImmutableList<Term>,
                                                  ImmutableList<Term>>>> respects,
                             Term variant, 
                             Term selfTerm,
                             ImmutableList<Term> localIns,
                             ImmutableList<Term> localOuts,
                             Map<LocationVariable,Term> atPres) {
        assert loop != null;
        //assert modifies != null;
        //assert heapAtPre != null;
        this.loop                       = loop;
        this.pm                         = pm;
        this.innermostExecCont          = innermostExecCont;
        this.guard                      = null;
        this.originalInvariants         =
                invariants == null ? new LinkedHashMap<LocationVariable,Term>() : invariants;
        this.originalVariant            = variant;
        this.originalModifies           =
                modifies == null ? new LinkedHashMap<LocationVariable,Term>() : modifies;
        this.originalRespects           =
                respects == null ? new LinkedHashMap<LocationVariable,
                                                     ImmutableList<Triple<ImmutableList<Term>,
                                                                          ImmutableList<Term>,
                                                                          ImmutableList<Term>>>>()
                                 : respects;
        this.originalSelfTerm           = selfTerm;
        this.localIns                   = localIns;
        this.localOuts                  = localOuts;
        this.originalAtPres             =
                atPres == null ? new LinkedHashMap<LocationVariable,Term>() : atPres;
    }
    
    public LoopInvariantImpl(LoopStatement loop,
                             Map<LocationVariable,Term> invariants,
                             Map<LocationVariable,Term> modifies,
                             Map<LocationVariable,
                             ImmutableList<Triple<ImmutableList<Term>,
                             ImmutableList<Term>,
                             ImmutableList<Term>>>> respects,
                             Term variant, 
                             Term selfTerm,
                             ImmutableList<Term> localIns,
                             ImmutableList<Term> localOuts,
                             Map<LocationVariable,Term> atPres) {
        this(loop, null, null, invariants, modifies, respects, variant, selfTerm,
             localIns, localOuts, atPres);
    }

    public LoopInvariantImpl(LoopStatement loop,
                             Map<LocationVariable,Term> invariants,
                             Map<LocationVariable,Term> modifies,   
                             Term variant,
                             Term selfTerm,                             
                             ImmutableList<Term> localIns,
                             ImmutableList<Term> localOuts,
                             Map<LocationVariable,Term> atPres) {
        this(loop, invariants, modifies, null, variant, selfTerm, localIns, localOuts, atPres);
    }
    
    public LoopInvariantImpl(LoopStatement loop,
                             Map<LocationVariable,Term> invariants,
                             Map<LocationVariable,Term> modifies,   
                             Term variant,
                             Term selfTerm,
                             Map<LocationVariable,Term> atPres) {
        this(loop, invariants, modifies, null, variant, selfTerm,
             ImmutableSLList.<Term>nil(),ImmutableSLList.<Term>nil(), atPres);
    }
    
    /**
     * Creates an empty, default loop invariant for the passed loop.
     */
    public LoopInvariantImpl(LoopStatement loop, 
	    		     Term selfTerm, 
	    		     Map<LocationVariable,Term> atPres) {
        this(loop, 
             null, 
             null,
             null,
             null,             
             selfTerm,
             null,
             null,
             atPres);
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
          for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
             if(atPres.get(h) != null && originalAtPres.get(h) != null) {
                 assert originalAtPres.get(h).sort().equals(atPres.get(h).sort());
                 result.put(originalAtPres.get(h), atPres.get(h));
             }
          }
        }

        return result;
    }
    
    
    private Map<Term,Term> getInverseReplaceMap(
            Term selfTerm,
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
    public IProgramMethod getTarget() {
        return pm;
    }
    
    @Override
    public ExecutionContext getExecutionContext() {
        return innermostExecCont;
    }

    @Override
    public Term getGuard() {        
        return guard;
    }

    @Override    
    public Term getInvariant(LocationVariable heap,
                             Term selfTerm,
            		     Map<LocationVariable,Term> atPres,
            		     Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalInvariants.get(heap));
    }
    
    @Override
    public Term getInvariant(Term selfTerm, Map<LocationVariable,Term> atPres, Services services){
        assert (selfTerm == null) == (originalSelfTerm == null);
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap);
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
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalModifies.get(heap));
    }
    
    @Override
    public Term getModifies(Term selfTerm, Map<LocationVariable,Term> atPres, Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalModifies.get(baseHeap));
    }

    @Override
    public ImmutableList<Triple<ImmutableList<Term>,
                                ImmutableList<Term>,
                                ImmutableList<Term>>> getRespects(LocationVariable heap,
                                                                  Term selfTerm,
                                                                  Map<LocationVariable,Term> atPres,
                                                                  Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replaceTriples(originalRespects.get(heap));
    }

    @Override
    public ImmutableList<Triple<ImmutableList<Term>,
                                ImmutableList<Term>,
                                ImmutableList<Term>>> getRespects(LocationVariable heap) {
        ImmutableList<Triple<ImmutableList<Term>,
                             ImmutableList<Term>,
                             ImmutableList<Term>>>
            respects = ImmutableSLList.<Triple<ImmutableList<Term>,
                                               ImmutableList<Term>,
                                               ImmutableList<Term>>>nil();
        return respects.append(originalRespects.get(heap)); // apparently respects can be null
    }
    
    @Override
    public ImmutableList<Triple<ImmutableList<Term>,
                                ImmutableList<Term>,
                                ImmutableList<Term>>> getRespects(Services services) {
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        return getRespects(baseHeap);
    }

    @Override
    public Term getVariant(Term selfTerm, 
            		   Map<LocationVariable,Term> atPres,
            		   Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap);
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
               ImmutableList<Triple<ImmutableList<Term>,
                                    ImmutableList<Term>,
                                    ImmutableList<Term>>>> getInternalRespects(){
        return originalRespects;
    }
    
    @Override
    public Term getInternalSelfTerm() {
        return originalSelfTerm;
    }

    @Override
    public ImmutableList<Term> getLocalIns() {
        return localIns;
    }

    @Override
    public ImmutableList<Term> getLocalOuts() {
        return localOuts;
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
    public LoopInvariant setLoop(LoopStatement loop) {        
        return new LoopInvariantImpl(loop,
                                     pm,
                                     innermostExecCont,
                                     originalInvariants,
                                     originalModifies,
                                     originalRespects,
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
                                     innermostExecCont,
                                     originalInvariants,
                                     originalModifies,
                                     originalRespects,
                                     originalVariant, 
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }
    
    @Override
    public LoopInvariant setExecutionContext(ExecutionContext execCont) {
        return new LoopInvariantImpl(loop,
                                     pm,
                                     execCont,
                                     originalInvariants,
                                     originalModifies,
                                     originalRespects,
                                     originalVariant, 
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }

    @Override
    public void setGuard(Term guardTerm, Services services) {
        assert this.guard == null;
        this.guard = guardTerm;
        
        ImmutableList<Triple<ImmutableList<Term>,
                             ImmutableList<Term>,
                             ImmutableList<Term>>> respects = getRespects(services);
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        originalRespects.remove(baseHeap);
        respects =
                respects.tail()
                    .prepend(new Triple<ImmutableList<Term>,
                                        ImmutableList<Term>,
                                        ImmutableList<Term>>
                    (respects.head().first.append(guardTerm),
                     respects.head().second,
                     respects.head().third));
        originalRespects.put(baseHeap, respects);
    }

    @Override
    public LoopInvariant setInvariant(Map<LocationVariable,Term> invariants, 
            			      Term selfTerm,
            			      Map<LocationVariable,Term> atPres,
            			      Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        Map<LocationVariable,Term> newInvariants = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : invariants.keySet()) {
           newInvariants.put(heap, or.replace(invariants.get(heap)));
        }
        return new LoopInvariantImpl(loop,
                                     pm,
                                     innermostExecCont,
                                     newInvariants,
                                     originalModifies,
                                     originalRespects,
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
                + "; respects: " 
                + originalRespects
                + "; variant: "
                + originalVariant
                + "; guard: "
                + (guard != null ? guard : "none")
                + "; input parameters: " 
                + localIns
                + "; output parameters: " 
                + localOuts;
    }

    @Override
    public String getPlainText(Services services) {
       return "invariants: " 
             + originalInvariants
             + ";\nmodifies: " 
             + originalModifies
             + ";\nvariant: "
             + originalVariant;
    }


    @Override
    public String getDisplayName() {
	return "Loop Invariant";
    }


    @Override
    public KeYJavaType getKJT() {
        assert (pm != null);
	return pm.getContainerType();
    }

    @Override
    public String getName() {
        return "Loop Invariant";
    }

    @Override
    public String getUniqueName() {
        if (pm != null)
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + getTarget().getFullName();
        else
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + Math.abs(getLoop().hashCode());
    }

    @Override
    public VisibilityModifier getVisibility() {
	assert false;
	return null;
    }
}
