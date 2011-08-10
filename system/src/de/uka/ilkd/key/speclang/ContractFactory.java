// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.speclang;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;

/**
 * Contracts should only be created through methods of this class
 * @author bruns
 *
 */
public class ContractFactory {

    private static final String INVALID_ID = "INVALID_ID";
    private static final String UNKNOWN_CONTRACT_IMPLEMENTATION = "unknown contract implementation";
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    private final Services services;
    private final TermBuilder tb = TermBuilder.DF;
    

    public ContractFactory (Services services){
        assert services != null;
        this.services = services;
    }

    // PUBLIC INTERFACE
    
    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a postcondition (regardless of termination case).
     */
    public FunctionalOperationContract addPost(FunctionalOperationContract old, Term addedPost,
            ProgramVariable selfVar, ProgramVariable resultVar, ProgramVariable excVar,
            ImmutableList<ProgramVariable> paramVars, LocationVariable heapAtPreVar){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
    FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
    addedPost = replaceVariables(addedPost, selfVar, resultVar, excVar, paramVars, heapAtPreVar, 
            foci.originalSelfVar, foci.originalResultVar, foci.originalExcVar, foci.originalParamVars, foci.originalHeapAtPreVar);

    //create new contract
    return new FunctionalOperationContractImpl(foci.baseName,
            foci.name,
            foci.kjt,                                    
            foci.pm,
            foci.modality,
            foci.originalPre,
            foci.originalMby,
            tb.and(foci.originalPost, addedPost),
            foci.originalMod,
            foci.originalSelfVar,
            foci.originalParamVars,
            foci.originalResultVar,
            foci.originalExcVar,
            foci.originalHeapAtPreVar,
            foci.id,
            foci.toBeSaved);
    }
    
    /** Add the specification contained in InitiallyClause as a postcondition. */
    public FunctionalOperationContract addPost(FunctionalOperationContract old, InitiallyClause ini){
        final ProgramVariable selfVar = tb.selfVar(services, ini.getKJT(), true);
        return addPost(old, ini.getClause(selfVar, services), null, null, null, null, null);
    }
    
    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a precondition.
     */
    public FunctionalOperationContract addPre(FunctionalOperationContract old, Term addedPre,
            ProgramVariable selfVar, 
            ImmutableList<ProgramVariable> paramVars){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
    FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
    addedPre = replaceVariables(addedPre, selfVar, paramVars, foci.originalSelfVar, foci.originalParamVars);

    //create new contract
    return new FunctionalOperationContractImpl(foci.baseName,
            foci.name,
            foci.kjt,                                    
            foci.pm,
            foci.modality,
            tb.and(foci.originalPre, addedPre),
            foci.originalMby,
            foci.originalPost,
            foci.originalMod,
            foci.originalSelfVar,
            foci.originalParamVars,
            foci.originalResultVar,
            foci.originalExcVar,
            foci.originalHeapAtPreVar,
            foci.id,
            foci.toBeSaved);
    }

    public DependencyContract dep(KeYJavaType containerType,
            ObserverFunction pm, Term requires, Term measuredBy, Term accessible,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars) {
        return dep("JML accessible clause", containerType, pm, requires, measuredBy, accessible, selfVar, paramVars);
    }
    
    public DependencyContract dep(KeYJavaType kjt, Triple<ObserverFunction, Term, Term> dep, ProgramVariable selfVar){
        final ImmutableList<ProgramVariable> paramVars =
                tb.paramVars(services, dep.first, false);
        return dep(kjt,dep.first,tb.inv(services, tb.var(selfVar)),dep.third,dep.second,selfVar,paramVars);
    }

    public DependencyContract dep(String string, KeYJavaType containerType,
            ObserverFunction pm, Term requires, Term measuredBy, Term accessible,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars) {
        return new DependencyContractImpl(string, containerType,pm, requires, measuredBy, accessible, selfVar, paramVars);
    }

    @Override
    public boolean equals (Object o){
        if (o instanceof ContractFactory){
            return MiscTools.equalsOrNull(services, ((ContractFactory)o).services);
        } else {
            return false;
        }
    }

    public FunctionalOperationContract func (ProgramMethod pm, InitiallyClause ini){
        try {
            return new JMLSpecFactory(services).initiallyClauseToContract(ini, pm);
        } catch (SLTranslationException e) {
            services.getExceptionHandler().reportException(e);
            return null;
        }
    }

    public FunctionalOperationContract func (String baseName,
            KeYJavaType kjt,       
            ProgramMethod pm,
            Modality modality,
            Term pre,
            Term mby,                           
            Term post,
            Term mod,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            LocationVariable heapAtPreVar,
            boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, kjt,   pm, modality, pre, mby, post, mod,selfVar, paramVars,resultVar,excVar,heapAtPreVar, toBeSaved);
    }
       
    
    public FunctionalOperationContract func (String baseName, ProgramMethod pm, boolean terminates, Term pre, Term mby, Term post, Term mod, ProgramVariableCollection pv ){
        Modality modality = terminates ? Modality.DIA : Modality.BOX;
        return func(baseName, pm, modality, pre, mby, post, mod,pv, false);
    }
    
    public FunctionalOperationContract func (String baseName, ProgramMethod pm,
            Modality modality, Term pre, Term mby, Term post, Term mod,
            ProgramVariableCollection progVars, boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, null, pm.getContainerType(), pm, modality, pre, mby,
                post, mod, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, progVars.heapAtPreVar,
                Contract.INVALID_ID, toBeSaved);
    }
    
 
    @SuppressWarnings("unchecked")
    public <T extends Contract> T setID(T old, int newId){
        if (old instanceof FunctionalOperationContractImpl){
            return (T) setID((FunctionalOperationContractImpl)old, newId);
        } else if (old instanceof DependencyContractImpl){
            return (T) setID((DependencyContractImpl)old, newId);
        } else {
            assert false : UNKNOWN_CONTRACT_IMPLEMENTATION;
            return null;
        }
    }
    
    
    public FunctionalOperationContract setModality(FunctionalOperationContract old, Modality modality){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        return new FunctionalOperationContractImpl(foci.baseName, foci.kjt, foci.pm, modality, foci.originalPre, foci.originalMby, foci.originalPost, foci.originalMod, foci.originalSelfVar, foci.originalParamVars, foci.originalResultVar, foci.originalExcVar, foci.originalHeapAtPreVar, foci.toBeSaved);
    }


    public FunctionalOperationContract setModifies(FunctionalOperationContract old, Term modifies){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        return new FunctionalOperationContractImpl(foci.baseName, foci.kjt, foci.pm, foci.modality, foci.originalPre, foci.originalMby, foci.originalPost, modifies, foci.originalSelfVar, foci.originalParamVars, foci.originalResultVar, foci.originalExcVar, foci.originalHeapAtPreVar, foci.toBeSaved);
    }
   
    @SuppressWarnings("unchecked")
    public <T extends Contract> T setTarget(T old, KeYJavaType newKJT, ObserverFunction newPM){
        if (old instanceof FunctionalOperationContractImpl){
            return (T) setTarget((FunctionalOperationContractImpl)old, newKJT, newPM);
        } else if (old instanceof DependencyContractImpl){
            return (T) setTarget((DependencyContractImpl)old, newKJT, newPM);
        } else {
            assert false : UNKNOWN_CONTRACT_IMPLEMENTATION;
            return null;
        }
    }
    
    /**
     * Returns the union of the passed contracts. 
     * Probably you want to use SpecificationRepository.combineContracts()
     * instead, which additionally takes care that the combined contract can be 
     * loaded later. The resulting contract has id "INVALID_ID".
     */
    public FunctionalOperationContract union(FunctionalOperationContract ... contracts){
        assert contracts[0] instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        
        FunctionalOperationContractImpl t = (FunctionalOperationContractImpl) contracts[0];
        FunctionalOperationContract[] others = Arrays.copyOfRange(contracts, 1, contracts.length);
        assert others != null;

        //determine names
        StringBuffer nameSB = new StringBuffer(t.getName());
        for(FunctionalOperationContract other : others) {
            nameSB.append(CONTRACT_COMBINATION_MARKER + other.getName());
        }
        
        for(FunctionalOperationContract contract : others) {
            assert contract.getTarget().equals(t.pm);
        }
        if(others.length == 0) {
            return t;
        }
        
        //collect information
        Term pre = t.originalPre;
        Term mby = t.originalMby;        
        Term post = tb.imp(atPreify(t.originalPre, 
                        t.originalHeapAtPreVar), 
                   t.originalPost);
        Term mod = t.originalMod;
        Modality moda = t.modality;
        for(FunctionalOperationContract other : others) {
            Term otherPre = other.getPre(t.originalSelfVar, 
                             t.originalParamVars, 
                             services);
            Term otherMby = other.hasMby()
                        ? other.getMby(t.originalSelfVar, 
                                   t.originalParamVars, 
                                   services)
                            : null;   
            Term otherPost = other.getPost(t.originalSelfVar, 
                               t.originalParamVars, 
                               t.originalResultVar, 
                               t.originalExcVar, 
                               t.originalHeapAtPreVar, 
                               services);
            Term otherMod = other.getMod(t.originalSelfVar, 
                                         t.originalParamVars, 
                                         services);

            pre = tb.or(pre, otherPre);
            mby = tb.ife(otherPre, otherMby, mby) ;         
            post = tb.and(post, tb.imp(atPreify(otherPre, 
                                t.originalHeapAtPreVar), 
                               otherPost));
            mod = mod == null ? otherMod
                    : (otherMod == null ?
                            mod : tb.union(services, mod, otherMod));
        }

        return new FunctionalOperationContractImpl(INVALID_ID,
                         nameSB.toString(),
                                         t.kjt,                        
                                         t.pm,
                                         moda,
                                         pre,
                                         mby,
                                         post,
                                         mod,
                                         t.originalSelfVar,
                                         t.originalParamVars,
                                         t.originalResultVar,
                                         t.originalExcVar,
                                         t.originalHeapAtPreVar,
                                         Contract.INVALID_ID,
                                         t.toBeSaved);
    }
    

    // PRIVATE METHODS
    
    private static <T> void addToMap(T var, T originalVar,
            Map<T,T> map) {
        if(var != null) {
            map.put(var, originalVar);
        }
    }

    private Term atPreify(Term t, ProgramVariable heapAtPreVar) {
        final Map<Term,Term> map = new HashMap<Term,Term>();
        map.put(tb.heap(services), tb.var(heapAtPreVar));
        return new OpReplacer(map).replace(t);
    }
     

    /** replace in original the variables used for self and parameters */
    private Term replaceVariables(Term original, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable originalSelfVar, ImmutableList<ProgramVariable> originalParamVars) {
        return replaceVariables(original, selfVar, null, null, paramVars, null, originalSelfVar, null, null, originalParamVars, null);
    }
    
    /** replace in original the variables used for self, result, exception, heap, and parameters */
    private Term replaceVariables(Term original, ProgramVariable selfVar, ProgramVariable resultVar, ProgramVariable excVar,
            ImmutableList<ProgramVariable> paramVars, LocationVariable heapAtPreVar,
            ProgramVariable originalSelfVar, ProgramVariable originalResultVar,ProgramVariable originalExcVar, ImmutableList<ProgramVariable> originalParamVars,
            LocationVariable originalHeapAtPreVar) {
        Map <Operator, Operator> map = new LinkedHashMap<Operator,Operator>();
        addToMap(selfVar, originalSelfVar, map);
        addToMap(resultVar, originalResultVar, map);
        addToMap(excVar, originalExcVar, map);
        addToMap(heapAtPreVar, originalHeapAtPreVar, map);
        
        if(paramVars != null) {
            Iterator<ProgramVariable> it1 = paramVars.iterator();
            Iterator<ProgramVariable> it2 = originalParamVars.iterator();
            while(it1.hasNext()) {
                assert it2.hasNext();
                map.put(it1.next(), it2.next());
            }
        }
        OpReplacer or = new OpReplacer(map);
        original = or.replace(original);
        return original;
    }
    
 
    
    private DependencyContractImpl setID(DependencyContractImpl dc, int newId) {
        return new DependencyContractImpl(dc.baseName,
                                      null,
                              dc.kjt,                                   
                              dc.target,
                              dc.originalPre,
                              dc.originalMby,                            
                              dc.originalDep,
                              dc.originalSelfVar,
                              dc.originalParamVars,
                              newId);   
    }
    
    
    private FunctionalOperationContractImpl setID(FunctionalOperationContractImpl foci, int newId) {
        return new FunctionalOperationContractImpl(foci.baseName,
                                     null,
                             foci.kjt,                                    
                             foci.pm,
                             foci.modality,
                             foci.originalPre,
                             foci.originalMby,
                             foci.originalPost,
                             foci.originalMod,
                             foci.originalSelfVar,
                             foci.originalParamVars,
                             foci.originalResultVar,
                             foci.originalExcVar,
                             foci.originalHeapAtPreVar,
                             newId,
                             foci.toBeSaved);    
    }        
    
    private DependencyContractImpl setTarget(DependencyContractImpl dc, KeYJavaType newKJT,
                                ObserverFunction newTarget) {
        return new DependencyContractImpl(dc.baseName,
                          null,
                              newKJT,                        
                              newTarget,
                              dc.originalPre,
                              dc.originalMby,                            
                              dc.originalDep,
                              dc.originalSelfVar,
                              dc.originalParamVars,
                              dc.id);  
    }


    private FunctionalOperationContractImpl setTarget(FunctionalOperationContractImpl foci, KeYJavaType newKJT,
                           ObserverFunction newPM) {
        return new FunctionalOperationContractImpl(foci.baseName,
                         null,
                             newKJT,                         
                             (ProgramMethod)newPM,
                             foci.modality,
                             foci.originalPre,
                             foci.originalMby,
                             foci.originalPost,
                             foci.originalMod,
                             foci.originalSelfVar,
                             foci.originalParamVars,
                             foci.originalResultVar,
                             foci.originalExcVar,
                             foci.originalHeapAtPreVar,
                             foci.id,
                             foci.toBeSaved && newKJT.equals(foci.kjt));  
    }
    
}
