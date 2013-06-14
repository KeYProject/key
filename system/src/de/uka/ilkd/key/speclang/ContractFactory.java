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

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
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
            ImmutableList<ProgramVariable> paramVars, Map<LocationVariable, LocationVariable> atPreVars){
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
    FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
    addedPost = replaceVariables(addedPost, selfVar, resultVar, excVar, paramVars, atPreVars,
            foci.originalSelfVar, foci.originalResultVar, foci.originalExcVar, foci.originalParamVars, foci.originalAtPreVars);

    Map<LocationVariable,Term> newPosts = new LinkedHashMap<LocationVariable,Term>();
    for(LocationVariable h : foci.originalPosts.keySet()) {
       if(h == services.getTypeConverter().getHeapLDT().getHeap()) {
          newPosts.put(h, tb.and(foci.originalPosts.get(h), addedPost));
       }else{
          newPosts.put(h, foci.originalPosts.get(h));
       }
    }

    //create new contract
    return new FunctionalOperationContractImpl(foci.baseName,
            foci.name,
            foci.kjt,
            foci.pm,
            foci.specifiedIn,
            foci.modality,
            foci.originalPres,
            foci.originalMby,
            newPosts,
            foci.originalMods,
            foci.hasRealModifiesClause,
            foci.originalSelfVar,
            foci.originalParamVars,
            foci.originalResultVar,
            foci.originalExcVar,
            foci.originalAtPreVars,
            foci.id,
            foci.toBeSaved,
            foci.transaction);
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
    public FunctionalOperationContract addPre(FunctionalOperationContract old,
                                              Term addedPre,
                                              ProgramVariable selfVar,
                                              ImmutableList<ProgramVariable> paramVars, Map<LocationVariable,LocationVariable> atPreVars) {
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci =
                (FunctionalOperationContractImpl) old;
        addedPre =
                replaceVariables(addedPre, selfVar, paramVars, atPreVars,
                                 foci.originalSelfVar, foci.originalParamVars, foci.originalAtPreVars);

      Map<LocationVariable,Term> newPres = new LinkedHashMap<LocationVariable,Term>();
      for(LocationVariable h : foci.originalPres.keySet()) {
         if(h == services.getTypeConverter().getHeapLDT().getHeap()) {
            newPres.put(h, tb.and(foci.originalPres.get(h), addedPre));
         }else{
            newPres.put(h, foci.originalPres.get(h));
         }
      }

        //create new contract
        return new FunctionalOperationContractImpl(foci.baseName,
                                                   foci.name,
                                                   foci.kjt,
                                                   foci.pm,
                                                   foci.specifiedIn,
                                                   foci.modality,
                                                   newPres,
                                                   foci.originalMby,
                                                   foci.originalPosts,
                                                   foci.originalMods,
                                                   foci.hasRealModifiesClause,
                                                   foci.originalSelfVar,
                                                   foci.originalParamVars,
                                                   foci.originalResultVar,
                                                   foci.originalExcVar,
                                                   foci.originalAtPreVars,
                                                   foci.id,
                                                   foci.toBeSaved,
                                                   foci.originalMods.get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null
                                                   );
    }

    public DependencyContract dep(KeYJavaType containerType,
                                  IObserverFunction pm,
                                  KeYJavaType specifiedIn,
                                  Term requires,
                                  Term measuredBy,
                                  Term accessible,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars) {
        assert (selfVar == null) == pm.isStatic();
        return dep("JML accessible clause", containerType, pm, specifiedIn,
                   requires, measuredBy, accessible, selfVar, paramVars);
    }

    public DependencyContract dep(KeYJavaType kjt,
                                  Triple<IObserverFunction, Term, Term> dep,
                                  ProgramVariable selfVar) {
        final ImmutableList<ProgramVariable> paramVars =
                tb.paramVars(services, dep.first, false);
        assert (selfVar == null) == dep.first.isStatic();
        if (selfVar != null) {
            return dep(kjt, dep.first, dep.first.getContainerType(), tb.inv(services, tb.var(selfVar)),
                       dep.third, dep.second, selfVar, paramVars);
        } else {
            // TODO: insert static invariant??
            return dep(kjt, dep.first, dep.first.getContainerType(), tb.tt(), dep.third, dep.second,
                       selfVar, paramVars);
        }
    }

    public DependencyContract dep(String string,
                                  KeYJavaType containerType,
                                  IObserverFunction pm,
                                  KeYJavaType specifiedIn,
                                  Term requires,
                                  Term measuredBy,
                                  Term accessible,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars) {
        assert (selfVar == null) == pm.isStatic();
        return new DependencyContractImpl(string, containerType, pm, specifiedIn,
                                          requires, measuredBy, accessible,
                                          selfVar, paramVars);
    }

    @Override
    public boolean equals (Object o){
        if (o instanceof ContractFactory){
            return MiscTools.equalsOrNull(services, ((ContractFactory)o).services);
        } else {
            return false;
        }
    }

    public FunctionalOperationContract func (IProgramMethod pm, InitiallyClause ini){
        try {
            return new JMLSpecFactory(services).initiallyClauseToContract(ini, pm);
        } catch (SLTranslationException e) {
            services.getExceptionHandler().reportException(e);
            return null;
        }
    }

    public FunctionalOperationContract func (String baseName,
            KeYJavaType kjt,
            IProgramMethod pm,
            Modality modality,
            Map<LocationVariable,Term> pres,
            Term mby,
            Map<LocationVariable,Term> posts,
            Map<LocationVariable,Term> mods,
            boolean hasMod,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable,LocationVariable> atPreVars,
            boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, kjt, pm, pm.getContainerType(), modality,
                pres, mby, posts, mods, hasMod, selfVar, paramVars,resultVar,excVar,atPreVars, toBeSaved,
                mods.get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null);
    }

    public FunctionalOperationContract func (String baseName, IProgramMethod pm, boolean terminates, Map<LocationVariable,Term> pres,
               Term mby, Map<LocationVariable,Term> posts, Map<LocationVariable,Term> mods, boolean hasMod, ProgramVariableCollection pv){
        return func(baseName, pm, terminates ? Modality.DIA : Modality.BOX, pres, mby, posts, mods, hasMod, pv, false, mods.get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null);
    }


    public FunctionalOperationContract func (String baseName, IProgramMethod pm,
            Modality modality, Map<LocationVariable,Term> pres, Term mby, Map<LocationVariable,Term> posts, Map<LocationVariable,Term> mods, boolean hasMod,
            ProgramVariableCollection progVars, boolean toBeSaved, boolean transaction) {
        return new FunctionalOperationContractImpl(baseName, null, pm.getContainerType(), pm, pm.getContainerType(), modality, pres, mby,
                posts, mods, hasMod, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, progVars.atPreVars,
                Contract.INVALID_ID, toBeSaved, transaction);
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
        Map<LocationVariable,Term> pres = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable h : t.originalPres.keySet()) {
           pres.put(h, t.originalPres.get(h));
        }
        Term mby = t.originalMby;
        Map<LocationVariable,Term> posts = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
           Term oriPost = t.originalPosts.get(h);
           if(oriPost != null) {
              posts.put(h,tb.imp(atPreify(t.originalPres.get(h),
                        t.originalAtPreVars),
                   oriPost));
           }
        }

        Map<LocationVariable,Term> mods = t.originalMods;
        boolean hasMod = t.hasModifiesClause();
        Modality moda = t.modality;
        for(FunctionalOperationContract other : others) {
            Term otherMby = other.hasMby()
                        ? other.getMby(t.originalSelfVar,
                                   t.originalParamVars,
                                   services)
                            : null;
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
              Term otherPre = other.getPre(h, t.originalSelfVar,
                               t.originalParamVars,
                               t.originalAtPreVars,
                               services);
              Term otherPost = other.getPost(h, t.originalSelfVar,
                                 t.originalParamVars,
                                 t.originalResultVar,
                                 t.originalExcVar,
                                 t.originalAtPreVars,
                                 services);
              if(h == services.getTypeConverter().getHeapLDT().getHeap()) {
                // bugfix (MU)
                // if the first or the other contract do not have a
                // measured-by-clause, assume no clause at all
                if(mby == null || otherMby == null) {
                  mby = null;
                } else {
                  mby = tb.ife(otherPre, otherMby, mby);
                }
              }
              if(otherPre != null) {
                pres.put(h,pres.get(h) == null ? otherPre : tb.or(pres.get(h), otherPre));
              }
              if(otherPost != null) {
                final Term oPost = tb.imp(atPreify(otherPre, t.originalAtPreVars), otherPost);
                posts.put(h, posts.get(h) == null ? oPost : tb.and(posts.get(h), oPost));
              }
            }

            boolean otherHasMod = other.hasModifiesClause();

            if(!hasMod && !otherHasMod) {
                // both contracts are strictly pure
                // hasMod remains false ...
                // no need to update mod.
            } else {
                hasMod = true;
                for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                   Term m1 = mods.get(h);
                   Term m2 = other.getMod(h,t.originalSelfVar,
                                         t.originalParamVars,
                                         services);
                   Term nm = null;
                   if(m1 == null && m2 == null)
                     continue;
                   if(m1 == null){
                     nm = m2;
                   }else if(m2 == null) {
                     nm = m1;
                   }else{
                     nm = tb.union(services, m1, m2);
                   }
                   mods.put(h, nm);
                }

            }
        }

        return new FunctionalOperationContractImpl(INVALID_ID,
                                                   nameSB.toString(),
                                                   t.kjt,
                                                   t.pm,
                                                   t.specifiedIn,
                                                   moda,
                                                   pres,
                                                   mby,
                                                   posts,
                                                   mods,
                                                   hasMod,
                                                   t.originalSelfVar,
                                                   t.originalParamVars,
                                                   t.originalResultVar,
                                                   t.originalExcVar,
                                                   t.originalAtPreVars,
                                                   Contract.INVALID_ID,
                                                   t.toBeSaved,
                                                   t.transaction);
    }


    // PRIVATE METHODS

    private static <T> void addToMap(T var, T originalVar,
            Map<T,T> map) {
        if(var != null) {
            map.put(var, originalVar);
        }
    }

    private Term atPreify(Term t, Map<LocationVariable,? extends ProgramVariable> atPreVars) {
        final Map<Term,Term> map = new LinkedHashMap<Term,Term>();
        for(LocationVariable h : atPreVars.keySet()) {
          if(atPreVars.get(h) != null) {
            map.put(tb.var(h), tb.var(atPreVars.get(h)));
          }
        }
        return new OpReplacer(map).replace(t);
    }


    /** replace in original the variables used for self and parameters */
    private Term replaceVariables(Term original, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Map<LocationVariable,LocationVariable> atPreVars,
            ProgramVariable originalSelfVar, ImmutableList<ProgramVariable> originalParamVars,
            Map<LocationVariable,LocationVariable> originalAtPreVars) {
        return replaceVariables(original,
                                selfVar, null, null, paramVars, atPreVars,
                                originalSelfVar, null, null, originalParamVars, originalAtPreVars);
    }

    /** replace in original the variables used for self, result, exception, heap, and parameters */
    private Term replaceVariables(Term original, ProgramVariable selfVar, ProgramVariable resultVar, ProgramVariable excVar,
            ImmutableList<ProgramVariable> paramVars, Map<LocationVariable,LocationVariable> atPreVars,
            ProgramVariable originalSelfVar, ProgramVariable originalResultVar,ProgramVariable originalExcVar, ImmutableList<ProgramVariable> originalParamVars,
            Map<LocationVariable,LocationVariable> originalAtPreVars) {
        Map <Operator, Operator> map = new LinkedHashMap<Operator,Operator>();
        addToMap(selfVar, originalSelfVar, map);
        addToMap(resultVar, originalResultVar, map);
        addToMap(excVar, originalExcVar, map);
        for(LocationVariable h : originalAtPreVars.keySet()) {
           if(atPreVars != null && atPreVars.get(h) != null ) {
             addToMap(atPreVars.get(h), originalAtPreVars.get(h), map);
           }
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


    public static String generateDisplayName(String baseName,
                                             KeYJavaType forClass,
                                             IObserverFunction target,
                                             KeYJavaType specifiedIn,
                                             int myId) {
        return baseName + " " + myId +
                (specifiedIn.equals(forClass)
                  ? ""
                  : " for "
                    + specifiedIn.getJavaType().getFullName());
    }


    public static String generateContractName(String baseName,
                                              KeYJavaType forClass,
                                              IObserverFunction target,
                                              KeYJavaType specifiedIn,
                                              int myId) {
        return generateContractTypeName(baseName, forClass, target, specifiedIn)
               + "." + myId;
    }


    public static String generateContractTypeName(String baseName,
                                                  KeYJavaType forClass,
                                                  IObserverFunction target,
                                                  KeYJavaType specifiedIn) {
        final String methodName = target.name().toString();
        final int startIndexShortName = methodName.indexOf("::") + 2;
        final String methodShortName = methodName.substring(startIndexShortName);
        return forClass.getJavaType().getFullName() + "[" +
               specifiedIn.getJavaType().getFullName() + "::" +
               methodShortName + "(" +
               concadinate(",", target.getParamTypes()) + ")" + "]"
               + "." + baseName;

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
