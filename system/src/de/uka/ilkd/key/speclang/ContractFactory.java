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

import de.uka.ilkd.key.collection.ImmutableArray;
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
            ImmutableList<ProgramVariable> paramVars, LocationVariable heapAtPreVar, LocationVariable savedHeapAtPreVar){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
    FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
    addedPost = replaceVariables(addedPost, selfVar, resultVar, excVar, paramVars, heapAtPreVar, savedHeapAtPreVar,
            foci.originalSelfVar, foci.originalResultVar, foci.originalExcVar, foci.originalParamVars, foci.originalHeapAtPreVar, foci.originalSavedHeapAtPreVar);

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
            foci.hasRealModifiesClause,
            foci.originalModBackup,
            foci.originalSelfVar,
            foci.originalParamVars,
            foci.originalResultVar,
            foci.originalExcVar,
            foci.originalHeapAtPreVar,
            foci.originalSavedHeapAtPreVar,
            foci.id,
            foci.toBeSaved);
    }
    
    /** Add the specification contained in InitiallyClause as a postcondition. */
    public FunctionalOperationContract addPost(FunctionalOperationContract old, InitiallyClause ini){
        final ProgramVariable selfVar = tb.selfVar(services, ini.getKJT(), true);
        return addPost(old, ini.getClause(selfVar, services), null, null, null, null, null, null);
    }
    
    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a precondition.
     */
    public FunctionalOperationContract addPre(FunctionalOperationContract old,
                                              Term addedPre,
                                              ProgramVariable selfVar,
                                              ImmutableList<ProgramVariable> paramVars, LocationVariable savedHeapAtPreVar) {
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci =
                (FunctionalOperationContractImpl) old;
        addedPre =
                replaceVariables(addedPre, selfVar, paramVars, savedHeapAtPreVar,
                                 foci.originalSelfVar, foci.originalParamVars, foci.originalSavedHeapAtPreVar);

        //create new contract
        return new FunctionalOperationContractImpl(foci.baseName,
                                                   foci.name,
                                                   foci.kjt,
                                                   foci.pm,
                                                   foci.modality,
                                                   tb.and(foci.originalPre,
                                                          addedPre),
                                                   foci.originalMby,
                                                   foci.originalPost,
                                                   foci.originalMod,
                                                   foci.hasRealModifiesClause,
                                                   foci.originalModBackup,
                                                   foci.originalSelfVar,
                                                   foci.originalParamVars,
                                                   foci.originalResultVar,
                                                   foci.originalExcVar,
                                                   foci.originalHeapAtPreVar,
                                                   foci.originalSavedHeapAtPreVar,
                                                   foci.id,
                                                   foci.toBeSaved);
    }

    public DependencyContract dep(KeYJavaType containerType,
                                  ObserverFunction pm,
                                  Term requires,
                                  Term measuredBy,
                                  Term accessible,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars) {
        assert (selfVar == null) == pm.isStatic();
        return dep("JML accessible clause", containerType, pm, requires,
                   measuredBy, accessible, selfVar, paramVars);
    }
    
    public DependencyContract dep(KeYJavaType kjt,
                                  Triple<ObserverFunction, Term, Term> dep,
                                  ProgramVariable selfVar) {
        final ImmutableList<ProgramVariable> paramVars =
                tb.paramVars(services, dep.first, false);
        assert (selfVar == null) == dep.first.isStatic();
        if (selfVar != null) {
            return dep(kjt, dep.first, tb.inv(services, tb.var(selfVar)),
                       dep.third, dep.second, selfVar, paramVars);
        } else {
            // TODO: insert static invariant??
            return dep(kjt, dep.first, tb.tt(), dep.third, dep.second,
                       selfVar, paramVars);
        }
    }

    public DependencyContract dep(String string,
                                  KeYJavaType containerType,
                                  ObserverFunction pm,
                                  Term requires,
                                  Term measuredBy,
                                  Term accessible,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars) {
        assert (selfVar == null) == pm.isStatic();
        return new DependencyContractImpl(string, containerType, pm, requires,
                                          measuredBy, accessible, selfVar,
                                          paramVars);
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
            boolean hasMod,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            LocationVariable heapAtPreVar,
            boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, kjt,   pm, modality, pre, mby, post, mod, hasMod, null, selfVar, paramVars,resultVar,excVar,heapAtPreVar, null, toBeSaved);
    }
       
    
    public FunctionalOperationContract func (String baseName, ProgramMethod pm, boolean terminates, Term pre, Term mby, Term post, Term mod, boolean hasMod, ProgramVariableCollection pv ){
        Modality modality = terminates ? Modality.DIA : Modality.BOX;
        return func(baseName, pm, modality, pre, mby, post, mod, hasMod, pv, false);
    }
    
    public FunctionalOperationContract func (String baseName, ProgramMethod pm,
            Modality modality, Term pre, Term mby, Term post, Term mod, boolean hasMod,
            ProgramVariableCollection progVars, boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, null, pm.getContainerType(), pm, modality, pre, mby,
                post, mod, hasMod, null, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, progVars.heapAtPreVar, progVars.savedHeapAtPreVar,
                Contract.INVALID_ID, toBeSaved);
    }
    
 
    public FunctionalOperationContract setModality(FunctionalOperationContract old, Modality modality){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        return new FunctionalOperationContractImpl(foci.baseName, foci.kjt, foci.pm, modality, foci.originalPre, foci.originalMby, foci.originalPost, foci.originalMod, foci.hasRealModifiesClause, foci.originalModBackup, foci.originalSelfVar, foci.originalParamVars, foci.originalResultVar, foci.originalExcVar, foci.originalHeapAtPreVar, foci.originalSavedHeapAtPreVar, foci.toBeSaved);
    }


    public FunctionalOperationContract setModifies(FunctionalOperationContract old, Term modifies){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        return new FunctionalOperationContractImpl(foci.baseName, foci.kjt, foci.pm, foci.modality, foci.originalPre, foci.originalMby, foci.originalPost, modifies, foci.hasRealModifiesClause, foci.originalModBackup, foci.originalSelfVar, foci.originalParamVars, foci.originalResultVar, foci.originalExcVar, foci.originalHeapAtPreVar, foci.originalSavedHeapAtPreVar, foci.toBeSaved);
    }
    
    public FunctionalOperationContract setHasModifiesClause(FunctionalOperationContract old, boolean hasModifiesClause){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        return new FunctionalOperationContractImpl(foci.baseName, foci.kjt, foci.pm, foci.modality, foci.originalPre, foci.originalMby, foci.originalPost, foci.originalMod, hasModifiesClause, foci.originalModBackup, foci.originalSelfVar, foci.originalParamVars, foci.originalResultVar, foci.originalExcVar, foci.originalHeapAtPreVar, foci.originalSavedHeapAtPreVar, foci.toBeSaved);
    }

    public FunctionalOperationContract setModifiesBackup(FunctionalOperationContract old, Term modifiesBackup){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        return new FunctionalOperationContractImpl(foci.baseName, foci.kjt, foci.pm, foci.modality, foci.originalPre, foci.originalMby, foci.originalPost, foci.originalMod, foci.hasRealModifiesClause, modifiesBackup, foci.originalSelfVar, foci.originalParamVars, foci.originalResultVar, foci.originalExcVar, foci.originalHeapAtPreVar, foci.originalSavedHeapAtPreVar, foci.toBeSaved);
    }

    public FunctionalOperationContract setSaveHeapAtPreVar(FunctionalOperationContract old, LocationVariable savedHeapAtPreVar){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        return new FunctionalOperationContractImpl(foci.baseName, foci.kjt, foci.pm, foci.modality, foci.originalPre, foci.originalMby, foci.originalPost, foci.originalMod, foci.hasRealModifiesClause, foci.originalModBackup, foci.originalSelfVar, foci.originalParamVars, foci.originalResultVar, foci.originalExcVar, foci.originalHeapAtPreVar, savedHeapAtPreVar, foci.toBeSaved);
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
        boolean hasMod = t.hasModifiesClause();
        Modality moda = t.modality;
        for(FunctionalOperationContract other : others) {
            Term otherPre = other.getPre(t.originalSelfVar, 
                             t.originalParamVars,
                             t.originalSavedHeapAtPreVar, 
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
                               t.originalSavedHeapAtPreVar, 
                               services);
            boolean otherHasMod = other.hasModifiesClause();
            Term otherMod = other.getMod(t.originalSelfVar, 
                                         t.originalParamVars, 
                                         services);

            pre = tb.or(pre, otherPre);
            
            // bugfix (MU)
            // if the first or the other contract do not have a
            // measured-by-clause, assume no clause at all 
            if(mby == null || otherMby == null) {
                mby = null;
            } else {
                mby = tb.ife(otherPre, otherMby, mby);
            }
            
            post = tb.and(post, tb.imp(atPreify(otherPre, 
                                t.originalHeapAtPreVar), 
                                otherPost));
            
            if(!hasMod && !otherHasMod) {
                // both contracts are strictly pure
                // hasMod remains false ...
                // no need to update mod.
            } else {
                hasMod = true;
                mod = mod == null ? otherMod
                    : (otherMod == null ?
                            mod : tb.union(services, mod, otherMod));
            }
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
                                         hasMod,
                                         null, // TODO !!!!
                                         t.originalSelfVar,
                                         t.originalParamVars,
                                         t.originalResultVar,
                                         t.originalExcVar,
                                         t.originalHeapAtPreVar,
                                         t.originalSavedHeapAtPreVar,
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
            ImmutableList<ProgramVariable> paramVars, LocationVariable savedHeapAtPreVar,
            ProgramVariable originalSelfVar, ImmutableList<ProgramVariable> originalParamVars, 
            LocationVariable originalSavedHeapAtPreVar) {
        return replaceVariables(original,
                                selfVar, null, null, paramVars, null, savedHeapAtPreVar,
                                originalSelfVar, null, null, originalParamVars, null, originalSavedHeapAtPreVar);
    }
    
    /** replace in original the variables used for self, result, exception, heap, and parameters */
    private Term replaceVariables(Term original, ProgramVariable selfVar, ProgramVariable resultVar, ProgramVariable excVar,
            ImmutableList<ProgramVariable> paramVars, LocationVariable heapAtPreVar, LocationVariable savedHeapAtPreVar,
            ProgramVariable originalSelfVar, ProgramVariable originalResultVar,ProgramVariable originalExcVar, ImmutableList<ProgramVariable> originalParamVars,
            LocationVariable originalHeapAtPreVar, LocationVariable originalSavedHeapAtPreVar) {
        Map <Operator, Operator> map = new LinkedHashMap<Operator,Operator>();
        addToMap(selfVar, originalSelfVar, map);
        addToMap(resultVar, originalResultVar, map);
        addToMap(excVar, originalExcVar, map);
        addToMap(heapAtPreVar, originalHeapAtPreVar, map);
        if(originalSavedHeapAtPreVar != null) {
           addToMap(savedHeapAtPreVar, originalSavedHeapAtPreVar, map);
        }        
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

    @Override
    public int hashCode() {
        return services == null ? 0 : services.hashCode();
    }
    
    
    public static String generateDisplayName(String myBaseName,
                                             int myId) {
        return myBaseName + " " + myId;
    }
    
    
    public static String generateContractName(String myBaseName,
                                              KeYJavaType myKjt,
                                              ObserverFunction myTarget,
                                              int myId) {
        return generateContractTypeName(myBaseName, myKjt, myTarget)
               + "." + myId;
    }


    public static String generateContractTypeName(String myBaseName,
                                                  KeYJavaType myKjt,
                                                  ObserverFunction myTarget) {
        return myKjt.getJavaType().getFullName() + "[" +
               myTarget + "(" +
               concadinate(",", myTarget.getParamTypes()) + ")" + "]"
               + "." + myBaseName;
               
    }
    
    
    private static String concadinate(String delim,
                                      ImmutableArray<KeYJavaType> elems) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < elems.size(); i++) {
            b.append(elems.get(i).getFullName());
            if (i + 1 < elems.size()) {
                b.append(delim);
            }
        }
        return b.toString();
    }
}
