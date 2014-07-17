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

import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProofSaver;
import static de.uka.ilkd.key.util.Assert.*;

/**
 * Standard implementation of the OperationContract interface.
 */
public class FunctionalOperationContractImpl implements FunctionalOperationContract {

    protected final TermBuilder TB; // TODO: Rename into tb
    private final TermServices services;

    final String baseName;
    final String name;
    final KeYJavaType kjt;
    final IProgramMethod pm;
    final KeYJavaType specifiedIn;
    final Modality modality;
    final Map<LocationVariable,Term> originalPres;
    final Term originalMby;
    final Map<LocationVariable,Term> originalPosts;
    final Map<LocationVariable,Term> originalAxioms;
    final Map<LocationVariable,Term> originalMods;
    final Map<ProgramVariable, Term> originalDeps;
    final ProgramVariable originalSelfVar;
    final ImmutableList<ProgramVariable> originalParamVars;
    final ProgramVariable originalResultVar;
    final ProgramVariable originalExcVar;
    final Map<LocationVariable,LocationVariable> originalAtPreVars;
    final Term globalDefs;
    final int id;
    final boolean transaction;
    final boolean toBeSaved;

    /**
     * If a method is strictly pure, it has no modifies clause which could
     * be anonymised.
     * @see #hasModifiesClause()
     */
    final Map<LocationVariable,Boolean> hasRealModifiesClause;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------


    /**
     * Creates an operation contract.
     * Using this constructor is discouraged: it may change in the future.
     * Please use the factory methods in {@link de.uka.ilkd.key.speclang.ContractFactory}.
     * @param baseName base name of the contract (does not have to be unique)
    * @param pm the IProgramMethod to which the contract belongs
    * @param modality the modality of the contract
    * @param mby the measured_by clause of the contract
    * @param selfVar the variable used for the receiver object
    * @param paramVars the variables used for the operation parameters
    * @param resultVar the variables used for the operation result
    * @param excVar the variable used for the thrown exception
    * @param globalDefs definitions for the whole contract
    * @param services TODO
    * @param pre the precondition of the contract
    * @param post the postcondition of the contract
    * @param mod the modifies clause of the contract
    * @param heapAtPreVar the variable used for the pre-heap
     */
    FunctionalOperationContractImpl(String baseName,
                                    String name,
                                    KeYJavaType kjt,
                                    IProgramMethod pm,
                                    KeYJavaType specifiedIn,
                                    Modality modality,
                                    Map<LocationVariable,Term> pres,
                                    Term mby,
                                    Map<LocationVariable,Term> posts,
                                    Map<LocationVariable,Term> axioms,
                                    Map<LocationVariable,Term> mods,
                                    Map<ProgramVariable, Term> accessibles,
                                    Map<LocationVariable,Boolean> hasRealMod,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    ProgramVariable resultVar,
                                    ProgramVariable excVar,
                                    Map<LocationVariable, LocationVariable> atPreVars,
                                    Term globalDefs,
                                    int id,
                                    boolean toBeSaved,
                                    boolean transaction, TermServices services) {
        assert !(name == null && baseName == null);
        assert kjt != null;
        assert pm != null;
        assert pres != null;
        assert posts != null;
        assert modality != null;
        assert (selfVar == null) == pm.isStatic();
        assert globalDefs == null || globalDefs.sort() == Sort.UPDATE;
        assert paramVars != null;
        assert paramVars.size() >= pm.getParameterDeclarationCount();
        // may be more parameters in specifications (ghost parameters)
        if (resultVar == null){
            assert (pm.isVoid() || pm.isConstructor()) : "resultVar == null for method "+pm;
        } else {
            assert (!pm.isVoid() && !pm.isConstructor()) : "non-null result variable for void method or constructor "+pm+" with return type "+pm.getReturnType();
        }
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        this.services = services;
        this.TB = services.getTermBuilder();
        this.baseName               = baseName;
        this.name = name != null
                ? name
                        : ContractFactory.generateContractName(baseName, kjt, pm, specifiedIn, id);
        this.pm          	    = pm;
        this.kjt                    = kjt;
        this.specifiedIn            = specifiedIn;
        this.modality               = modality;
        this.originalPres           = pres;
        this.originalMby            = mby;
        this.originalPosts          = posts;
        this.originalAxioms         = axioms;
        this.originalMods           = mods;
        this.originalDeps           = accessibles;
        this.hasRealModifiesClause  = hasRealMod;
        this.originalSelfVar        = selfVar;
        this.originalParamVars      = paramVars;
        this.originalResultVar      = resultVar;
        this.originalExcVar         = excVar;
        this.originalAtPreVars      = atPreVars;
        this.globalDefs             = globalDefs;
        this.id                     = id;
        this.transaction            = transaction;
        this.toBeSaved	            = toBeSaved;
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------


    protected Map<ProgramVariable, ProgramVariable>
                        getReplaceMap(ProgramVariable selfVar,
                                      ImmutableList<ProgramVariable> paramVars,
                                      ProgramVariable resultVar,
                                      ProgramVariable excVar,
                                      Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                                      Services services) {
        final Map<ProgramVariable, ProgramVariable> result =
                new LinkedHashMap<ProgramVariable, ProgramVariable>();

        //self
        if(selfVar != null) {
            assertSubSort(selfVar,originalSelfVar);
            result.put(originalSelfVar, selfVar);
        }

        //parameters
        if(paramVars != null) {
            assert originalParamVars.size() == paramVars.size();
            final Iterator<ProgramVariable> it1 = originalParamVars.iterator();
            final Iterator<ProgramVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                ProgramVariable paramVar         = it2.next();
                // allow contravariant parameter types
                assertSubSort(originalParamVar, paramVar);
                result.put(originalParamVar, paramVar);
            }
        }

        //result
        if(resultVar != null) {
            // workaround to allow covariant return types (bug #1384)
            assertSubSort(resultVar, originalResultVar);
            result.put(originalResultVar, resultVar);
        }

        //exception
        if(excVar != null) {
            assertEqualSort(originalExcVar, excVar);
            result.put(originalExcVar, excVar);
        }

        if(atPreVars != null) {
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            for(LocationVariable h : heapLDT.getAllHeaps()) {
                if(atPreVars.get(h) != null) {
                    assertEqualSort(originalAtPreVars.get(h), atPreVars.get(h));
                    result.put(originalAtPreVars.get(h), atPreVars.get(h));
                }
            }
        }

        return result;
    }


    @Deprecated
    protected Map<Term, Term> getReplaceMap(LocationVariable heap, Term heapTerm, Term selfTerm,
                                            ImmutableList<Term> paramTerms, Services services) {
        return getReplaceMap(heap, heapTerm, selfTerm, paramTerms, null, null, null, services);
    }

    @Deprecated
    protected Map<Term, Term> getReplaceMap(LocationVariable heap, Term heapTerm, Term selfTerm,
                                            ImmutableList<Term> paramTerms, Term resultTerm,
                                            Term excTerm, Term atPre, Services services) {
        Map<LocationVariable,Term> heapTerms = new LinkedHashMap<LocationVariable,Term>();
        heapTerms.put(heap, heapTerm);
        Map<LocationVariable,Term> atPres = new LinkedHashMap<LocationVariable,Term>();
        heapTerms.put(heap, atPre);
        return getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
    }

    protected Map<Term, Term> getReplaceMap(Map<LocationVariable,Term> heapTerms,
                                            Term selfTerm,
                                            ImmutableList<Term> paramTerms,
                                            Term resultTerm,
                                            Term excTerm,
                                            Map<LocationVariable, Term> atPres,
                                            Services services) {
        final Map<Term,Term> result = new LinkedHashMap<Term,Term>();

        //heaps

        for(LocationVariable heap : heapTerms.keySet()) {
            final Term heapTerm = heapTerms.get(heap);
            assert heapTerm == null || heapTerm.sort().equals(services.getTypeConverter()
                    .getHeapLDT()
                    .targetSort());
            result.put(TB.var(heap), heapTerm);
        }

        //self
        if(selfTerm != null) {
            assertSubSort(selfTerm, originalSelfVar);
            result.put(TB.var(originalSelfVar), selfTerm);
        }

        //parameters
        if(paramTerms != null) {
            assert originalParamVars.size() == paramTerms.size();
            final Iterator<ProgramVariable> it1 = originalParamVars.iterator();
            final Iterator<Term> it2 = paramTerms.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                Term paramTerm                   = it2.next();
                // TODO: what does this mean?
                assert paramTerm.sort().extendsTrans(originalParamVar.sort());
                result.put(TB.var(originalParamVar), paramTerm);
            }
        }

        //result
        if(resultTerm != null) {
            assertSubSort(resultTerm, originalResultVar);
            result.put(TB.var(originalResultVar), resultTerm);
        }

        //exception
        if(excTerm != null) {
            assertEqualSort(originalExcVar, excTerm);
            result.put(TB.var(originalExcVar), excTerm);
        }

        if(atPres != null) {
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            for(LocationVariable h : heapLDT.getAllHeaps()) {
                if(atPres.get(h) != null) {
                    assertEqualSort(originalAtPreVars.get(h), atPres.get(h));
                    result.put(TB.var(originalAtPreVars.get(h)), atPres.get(h));
                }
            }
        }
        return result;
    }


    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<ProgramVariable> addGhostParams(ImmutableList<ProgramVariable> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<ProgramVariable> ghostParams = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable param: originalParamVars) {
            if (param.isGhost())
                ghostParams = ghostParams.append(param);
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<Term> addGhostParamTerms(ImmutableList<Term> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<Term> ghostParams = ImmutableSLList.<Term>nil();
        for (ProgramVariable param: originalParamVars) {
            if (param.isGhost())
                ghostParams = ghostParams.append(TB.var(param));
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public String getName() {
        return name;
    }


    @Override
    public int id() {
        return id;
    }


    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }


    @Override
    public IProgramMethod getTarget() {
        return pm;
    }


    @Override
    public boolean hasMby() {
        return originalMby != null;
    }


    @Override
    public Term getPre(LocationVariable heap,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null : "null parameters";
        assert services != null;

        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size() : "number of parameters does not match";

        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                                                                               paramVars,
                                                                               null,
                                                                               null,
                                                                               atPreVars,
                                                                               services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalPres.get(heap));
    }


    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        Term result = null;
        for(LocationVariable heap : heapContext) {
            final Term p = getPre(heap, selfVar, paramVars, atPreVars, services);
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;
    }


    @Override
    public Term getPre(LocationVariable heap,
                       Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Map<LocationVariable,Term> atPres,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable,Term> heapTerms = new LinkedHashMap<LocationVariable, Term>();
        heapTerms.put(heap, heapTerm);

	final Map<Term, Term> replaceMap = getReplaceMap(heapTerms,
	                                                 selfTerm,
	                                                 paramTerms,
	                                                 null,
	                                                 null,
	                                                 atPres,
	                                                 services);
	final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
	return or.replace(originalPres.get(heap));
    }


    public Term getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable,Term> heapTerms,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Map<LocationVariable,Term> atPres,
                       Services services) {
        Term result = null;
        for(LocationVariable heap : heapContext) {
            final Term p = getPre(heap, heapTerms.get(heap), selfTerm, paramTerms, atPres, services);
            if(p == null) {
                continue;
            }
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;
    }


    @Override
    public Term getRequires(LocationVariable heap) {
        return originalPres.get(heap);
    }


    @Override
    public Term getEnsures(LocationVariable heap) {
        return originalPosts.get(heap);
    }


    @Override
    public Term getAssignable(LocationVariable heap) {
        return originalMods.get(heap);
    }

    @Override
    public Term getAccessible(ProgramVariable heap) {
        return originalDeps.get(heap);
    }

    @Override
    public Term getMby() {
        return this.originalMby;
    }

    @Override
    public Term getMby(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
	                                                                       paramVars,
	                                                                       null,
	                                                                       null,
	                                                                       null,
	                                                                       services);
	final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
	return or.replace(originalMby);
    }


    @Override
    public Term getMby(Map<LocationVariable,Term> heapTerms, Term selfTerm,
                       ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                       Services services) {
        assert heapTerms != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
	final Map<Term, Term> replaceMap = getReplaceMap(heapTerms,
	                                                 selfTerm,
	                                                 paramTerms,
	                                                 null,
	                                                 null,
	                                                 atPres,
	                                                 services);
	final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
	return or.replace(originalMby);
    }

    @Override
    public String getPlainText(Services services) {
        return getText(false, services);
    }

    @Override
    public String getHTMLText(Services services) {
        return getText(true, services);
    }

    private String getText(boolean includeHtmlMarkup, Services services) {
       return getText(pm, 
                      originalResultVar, 
                      originalSelfVar, 
                      originalParamVars, 
                      originalExcVar, 
                      hasMby(), 
                      originalMby, 
                      originalMods, 
                      hasRealModifiesClause, 
                      globalDefs, 
                      originalPres, 
                      originalPosts, 
                      originalAxioms, 
                      getModality(), 
                      transactionApplicableContract(), 
                      includeHtmlMarkup, 
                      services);
    }
    
    public static String getText(FunctionalOperationContract contract,
                                 ImmutableList<Term> contractParams,
                                 Term resultTerm,
                                 Term contractSelf,
                                 Term excTerm,
                                 LocationVariable baseHeap,
                                 Term baseHeapTerm,
                                 List<LocationVariable> heapContext,
                                 Map<LocationVariable,Term> atPres,
                                 boolean includeHtmlMarkup, 
                                 Services services) {
       ProgramVariable originalSelfVar = contractSelf != null ? (ProgramVariable)contractSelf.op() : null;
       ProgramVariable originalResultVar = resultTerm != null ? (ProgramVariable)resultTerm.op() : null;
       
       Map<LocationVariable, Term> heapTerms = new LinkedHashMap<LocationVariable,Term>();
       for(LocationVariable h : heapContext) {
          heapTerms.put(h, services.getTermBuilder().var(h));
       }
       
       Term originalMby = contract.hasMby()
             ? contract.getMby(heapTerms,
                   contractSelf,
                   contractParams,
                   atPres,
                   services)
           : null;
       
       Map<LocationVariable,Term> originalMods = new HashMap<LocationVariable, Term>();
       for(LocationVariable heap : heapContext) {
          Term m = contract.getMod(heap, services.getTermBuilder().var(heap), contractSelf,contractParams, services);
          originalMods.put(heap, m);
       }
       
       Map<LocationVariable,Boolean> hasRealModifiesClause = new HashMap<LocationVariable, Boolean>();
       for (LocationVariable heap : heapContext) {
          hasRealModifiesClause.put(heap, contract.hasModifiesClause(heap));
       }
       
       Term globalDefs = contract.getGlobalDefs(baseHeap, baseHeapTerm, contractSelf, contractParams, services);
       
       Map<LocationVariable,Term> originalPres = new HashMap<LocationVariable, Term>();
       for (LocationVariable heap : heapContext) {
          Term preTerm = contract.getPre(heap, heapTerms.get(heap), contractSelf, contractParams, atPres, services);
          originalPres.put(heap, preTerm);
       }
       
       Map<LocationVariable,Term> originalPosts = new HashMap<LocationVariable, Term>();
       for(LocationVariable heap : heapContext) {
          Term p = contract.getPost(heap, heapTerms.get(heap), contractSelf, contractParams, resultTerm, excTerm, atPres, services);
          originalPosts.put(heap, p);
       }

       Map<LocationVariable, ProgramVariable> atPresVars = new HashMap<LocationVariable, ProgramVariable>();
       for (Entry<LocationVariable, Term> entry : atPres.entrySet()) {
          if (entry.getValue() != null) {
             atPresVars.put(entry.getKey(), (ProgramVariable)entry.getValue().op());
          }
          else {
             atPresVars.put(entry.getKey(), null);
          }
       }
       
       Map<LocationVariable,Term> originalAxioms = new HashMap<LocationVariable, Term>();
       for(LocationVariable heap : heapContext) {
          Term p = contract.getRepresentsAxiom(heap, heapTerms.get(heap), contractSelf, contractParams, resultTerm, excTerm, atPres, services);
          originalAxioms.put(heap, p);
       }
       
       return getText(contract.getTarget(), 
                      originalResultVar, 
                      originalSelfVar, 
                      contractParams, 
                      (ProgramVariable)excTerm.op(), 
                      contract.hasMby(), 
                      originalMby, 
                      originalMods, 
                      hasRealModifiesClause, 
                      globalDefs, 
                      originalPres, 
                      originalPosts, 
                      originalAxioms, 
                      contract.getModality(), 
                      contract.transactionApplicableContract(), 
                      includeHtmlMarkup, 
                      services);
    }

    private static String getText(IProgramMethod pm, 
                                  ProgramVariable originalResultVar, 
                                  ProgramVariable originalSelfVar, 
                                  ImmutableList<? extends SVSubstitute> originalParamVars,
                                  ProgramVariable originalExcVar,
                                  boolean hasMby,
                                  Term originalMby,
                                  Map<LocationVariable,Term> originalMods,
                                  Map<LocationVariable,Boolean> hasRealModifiesClause,
                                  Term globalDefs,
                                  Map<LocationVariable,Term> originalPres,
                                  Map<LocationVariable,Term> originalPosts,
                                  Map<LocationVariable,Term> originalAxioms,
                                  Modality modality,
                                  boolean transaction,
                                  boolean includeHtmlMarkup, 
                                  Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();
        final StringBuffer sig = new StringBuffer();
        if (originalResultVar != null) {
            sig.append(originalResultVar);
            sig.append(" = ");
        }
        else if (pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(" = new ");
        }
        if (!pm.isStatic() && !pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(".");
        }
        sig.append(pm.getName());
        sig.append("(");
        for (SVSubstitute subst : originalParamVars) {
           if (subst instanceof Named) {
              Named named = (Named)subst;
              sig.append(named.name()).append(", ");
           }
           else if (subst instanceof Term) {
              sig.append(ProofSaver.printAnything(subst, services)).append(", ");
           }
           else {
              sig.append(subst).append(", ");
           }
        }
        if (!originalParamVars.isEmpty()) {
            sig.setLength(sig.length() - 2);
        }
        sig.append(")");
        if(!pm.isModel()) {
            sig.append(" catch(");
            sig.append(originalExcVar);
            sig.append(")");
        }

        final String mby = hasMby ? LogicPrinter.quickPrintTerm(originalMby, services) : null;

        String mods = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            if (originalMods.get(h) != null) {
                String printMods = LogicPrinter.quickPrintTerm(originalMods.get(h), services);
                mods = mods
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "mod"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printMods, false) : printMods.trim());
                if (!hasRealModifiesClause.get(h)) {
                    mods = mods +
                            (includeHtmlMarkup ? "<b>" : "") +
                            ", creates no new objects" +
                            (includeHtmlMarkup ? "</b>" : "");
                }
            }
        }

        String globalUpdates = "";
        if (globalDefs!=null){
            final String printUpdates = LogicPrinter.quickPrintTerm(globalDefs,services);
            globalUpdates = (includeHtmlMarkup? "<br><b>": "\n")
                    + "defs" + (includeHtmlMarkup? "</b> " : ": ")
                    + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printUpdates,false) : printUpdates.trim());
        }

        String pres = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            if (originalPres.get(h) != null) {
                String printPres = LogicPrinter.quickPrintTerm(originalPres.get(h), services);
                pres = pres
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "pre"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPres, false) : printPres.trim());
            }
        }

        String posts = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            if (originalPosts.get(h) != null) {
                String printPosts = LogicPrinter.quickPrintTerm(originalPosts.get(h), services);
                posts = posts
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "post"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPosts, false) : printPosts.trim());
            }
        }

        String axioms = "";
        if (originalAxioms != null) {
            for(LocationVariable h : heapLDT.getAllHeaps()) {
                if(originalAxioms.get(h) != null) {
                    String printAxioms = LogicPrinter.quickPrintTerm(originalAxioms.get(h), services);
                    posts = posts
                            + (includeHtmlMarkup ? "<br><b>" : "\n")
                            + "axiom"
                            + (h == baseHeap ? "" : "[" + h + "]")
                            + (includeHtmlMarkup ? "</b> " : ": ")
                            + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printAxioms, false) : printAxioms.trim());
                }
            }
        }

        if (includeHtmlMarkup) {
            return "<html>"
                    + "<i>"
                    + LogicPrinter.escapeHTML(sig.toString(), false)
                    + "</i>"
                    + globalUpdates
                    + pres
                    + posts
                    + axioms
                    + mods
                    + (hasMby ? "<br><b>measured-by</b> "+ LogicPrinter.escapeHTML(mby, false) : "")
                    + "<br><b>termination</b> "
                    + modality
                    + (transaction ? "<br><b>transaction applicable</b>" : "") +
                    "</html>";

        }
        else {
            return sig.toString()
                    + globalUpdates
                    + pres
                    + posts
                    + axioms
                    + mods
                    + (hasMby ? "\nmeasured-by: "+ mby : "")
                    + "\ntermination: "
                    + modality
                    + (transaction ? "\ntransaction applicable:" : "");
        }
    }


    @Override
    public boolean toBeSaved() {
        return toBeSaved;
    }


    @Override
    public String proofToString(Services services) {
        assert toBeSaved;
        final StringBuffer sb = new StringBuffer();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();
        sb.append(baseName).append(" {\n");

        //print var decls
        sb.append("  \\programVariables {\n");
        if(originalSelfVar != null) {
            sb.append("    ").append(originalSelfVar.proofToString());
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            sb.append("    ").append(originalParamVar.proofToString());
        }
        if(originalResultVar != null) {
            sb.append("    ").append(originalResultVar.proofToString());
        }
        sb.append("    ").append(originalExcVar.proofToString());
        sb.append("    ").append(originalAtPreVars.get(baseHeap).proofToString());
        sb.append("  }\n");

        //prepare Java program
        final Expression[] args
        = new ProgramVariable[originalParamVars.size()];
        int i = 0;
        for(ProgramVariable arg : originalParamVars) {
            args[i++] = arg;
        }
        final MethodReference mr
        = new MethodReference(new ImmutableArray<Expression>(args),
                pm.getProgramElementName(),
                originalSelfVar);
        final Statement callStatement;
        if(originalResultVar == null) {
            callStatement = mr;
        } else {
            callStatement = new CopyAssignment(originalResultVar, mr);
        }
        final CatchAllStatement cas
        = new CatchAllStatement(new StatementBlock(callStatement),
                (LocationVariable)originalExcVar);
        final StatementBlock sblock = new StatementBlock(cas);
        final JavaBlock jb = JavaBlock.createJavaBlock(sblock);

        //print contract term
        final Term update
        = TB.tf().createTerm(
                ElementaryUpdate.getInstance(originalAtPreVars.get(baseHeap)),
                TB.getBaseHeap());
        final Term modalityTerm
        = TB.tf().createTerm(modality,
                new Term[]{originalPosts.get(baseHeap)},
                new ImmutableArray<QuantifiableVariable>(),
                jb);
        final Term updateTerm
        = TB.tf().createTerm(UpdateApplication.UPDATE_APPLICATION,
                update,
                modalityTerm);
        final Term contractTerm
        = TB.tf().createTerm(Junctor.IMP, originalPres.get(baseHeap), updateTerm);
        final LogicPrinter lp = new LogicPrinter(new ProgramPrinter(),
                new NotationInfo(),
                null);
        try {
            lp.printTerm(contractTerm);
        } catch(IOException e) {
            throw new RuntimeException(e);
        }
        sb.append(lp.toString());

        //print modifies
        lp.reset();
        try {
            lp.printTerm(originalMods.get(baseHeap));
        } catch(IOException e) {
            throw new RuntimeException(e);
        }
        sb.append("  \\modifies ").append(lp.toString());

        sb.append("};\n");
        return sb.toString();
    }


    @Override
    public Modality getModality() {
        return modality;
    }

    @Override
    public Term getPost(LocationVariable heap,
                        ProgramVariable selfVar,
                        ImmutableList<ProgramVariable> paramVars,
                        ProgramVariable resultVar,
                        ProgramVariable excVar,
                        Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                        Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                paramVars,
                resultVar,
                excVar,
                atPreVars,
                services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalPosts.get(heap));
    }

    public Term getPost(List<LocationVariable> heapContext,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable,? extends ProgramVariable> atPreVars,
            Services services) {
        Term result = null;
        for(LocationVariable heap : heapContext) {
            final Term p = getPost(heap, selfVar, paramVars, resultVar, excVar, atPreVars, services);
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;

    }

    @Override
    public Term getPost(LocationVariable heap,
                        Term heapTerm,
                        Term selfTerm,
                        ImmutableList<Term> paramTerms,
                        Term resultTerm,
                        Term excTerm,
                        Map<LocationVariable, Term> atPres,
                        Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable,Term> heapTerms = new LinkedHashMap<LocationVariable, Term>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap = getReplaceMap(heapTerms,
                                                         selfTerm,
                                                         paramTerms,
                                                         resultTerm,
                                                         excTerm,
                                                         atPres,
                                                         services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalPosts.get(heap));
    }

    public Term getPost(List<LocationVariable> heapContext,
                        Map<LocationVariable,Term> heapTerms,
                        Term selfTerm,
                        ImmutableList<Term> paramTerms,
                        Term resultTerm,
                        Term excTerm,
                        Map<LocationVariable, Term> atPres,
                        Services services) {
        Term result = null;
        for(LocationVariable heap : heapContext) {
            final Term p = getPost(heap, heapTerms.get(heap), selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
            if(p == null) {
                continue;
            }
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;
    }

    @Override
    public Term getRepresentsAxiom(LocationVariable heap,
                                   ProgramVariable selfVar,
                                   ImmutableList<ProgramVariable> paramVars,
                                   ProgramVariable resultVar,
                                   Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                                   Services services) {
        assert (selfVar == null) == (originalSelfVar == null):
            "Illegal instantiation:" + (originalSelfVar == null?
                            "this is a static contract, instantiated with self variable '"+selfVar+"'"
                            : "this is an instance contract, instantiated without a self variable");
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert atPreVars.size() != 0;
        assert services != null;
        if(originalAxioms == null) {
            return null;
        }
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                paramVars,
                resultVar,
                null,
                atPreVars,
                services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalAxioms.get(heap));
    }

    @Override
    public Term getRepresentsAxiom(LocationVariable heap, 
                                   Term heapTerm, 
                                   Term selfTerm, 
                                   ImmutableList<Term> paramTerms, 
                                   Term resultTerm, 
                                   Term excTerm,
                                   Map<LocationVariable, Term> atPres, 
                                   Services services) {
       assert heapTerm != null;
       assert (selfTerm == null) == (originalSelfVar == null);
       assert paramTerms != null;
       paramTerms = addGhostParamTerms(paramTerms);
       assert paramTerms.size() == originalParamVars.size();
       assert (resultTerm == null) == (originalResultVar == null);
       assert pm.isModel() || excTerm != null;
       assert atPres.size() != 0;
       assert services != null;
       final Map<LocationVariable,Term> heapTerms = new LinkedHashMap<LocationVariable, Term>();
       heapTerms.put(heap, heapTerm);

       final Map<Term, Term> replaceMap = getReplaceMap(heapTerms,
               selfTerm,
               paramTerms,
               resultTerm,
               excTerm,
               atPres,
               services);
       final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
       return or.replace(originalAxioms.get(heap));
    }

    public boolean isReadOnlyContract(Services services) {
        return originalMods.get(services.getTypeConverter().getHeapLDT().getHeap()).op() ==
                services.getTypeConverter().getLocSetLDT().getEmpty();
    }

    public Term getAnyMod(Term mod, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                                                                               paramVars,
                                                                               null,
                                                                               null,
                                                                               null,
                                                                               services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(mod);
    }

    @Override
    public Term getMod(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services) {
        return getAnyMod(this.originalMods.get(heap), selfVar, paramVars, services);
    }

    private Term getAnyMod(LocationVariable heap, Term mod, Term heapTerm,
            Term selfTerm,
            ImmutableList<Term> paramTerms,
            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable,Term> heapTerms = new LinkedHashMap<LocationVariable, Term>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap = getReplaceMap(heapTerms,
                                                         selfTerm,
                                                         paramTerms,
                                                         null,
                                                         null,
                                                         null,
                                                         services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(mod);
    }

    @Override
    public boolean hasModifiesClause(LocationVariable heap) {
        return this.hasRealModifiesClause.get(heap);
    }

    @Override
    public Term getMod(LocationVariable heap, Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        return getAnyMod(heap, this.originalMods.get(heap), heapTerm, selfTerm, paramTerms, services);
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable,? extends ProgramVariable> atPreVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        if (originalSelfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(originalParamVar, paramVars.head());
            paramVars = paramVars.tail();
        }
        if(atPreVars != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(atPreVars.get(h) != null && originalAtPreVar != null) {
                    map.put(TB.var(atPre ? h : originalAtPreVar), TB.var(atPreVars.get(h)));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }


    @Override
    public Term getDep(LocationVariable heap, boolean atPre,
                       Term heapTerm, Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Map<LocationVariable, Term> atPres,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        map.put(TB.var(heap), heapTerm);
        if (originalSelfVar != null) {
            map.put(TB.var(originalSelfVar), selfTerm);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(TB.var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if(atPres != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(originalAtPreVar != null && atPres.get(h) != null) {
                    map.put(TB.var(originalAtPreVar), atPres.get(h));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }

    @Override
    public Term getGlobalDefs() {
        return this.globalDefs;
    }

    @Override
    public Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
                              ImmutableList<Term> paramTerms, Services services) {
        if (globalDefs==null) return null;
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        final Map<Term, Term> replaceMap = getReplaceMap(heap, heapTerm,
                selfTerm,
                paramTerms,
                services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(globalDefs);
    }

    @Override
    public String toString() {
        return
                (globalDefs == null? "": "defs: "+ globalDefs +"; ")
                + "pre: "
                + originalPres
                + "; mby: "
                + originalMby
                + "; post: "
                + originalPosts
                + "; mods: "
                + originalMods
                + "; hasMod: "
                + hasRealModifiesClause
                + (originalAxioms != null && originalAxioms.size() > 0 ?  ("; axioms: " + originalAxioms) : "")
                + "; termination: "
                + getModality()
                + "; transaction: "
                + transactionApplicableContract();
    }


    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        return new FunctionalOperationContractPO(initConfig,
                (FunctionalOperationContract) contract);
    }


    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, kjt, pm, specifiedIn, id);
    }


    @Override
    public VisibilityModifier getVisibility() {
        assert false; // this is currently not applicable for contracts
        return null;
    }

    public boolean transactionApplicableContract() {
        return transaction;
    }

    @Override
    public FunctionalOperationContract setID(int newId) {
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   kjt,
                                                   pm,
                                                   specifiedIn,
                                                   modality,
                                                   originalPres,
                                                   originalMby,
                                                   originalPosts,
                                                   originalAxioms,
                                                   originalMods,
                                                   originalDeps,
                                                   hasRealModifiesClause,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalAtPreVars,
                                                   globalDefs,
                                                   newId,
                                                   toBeSaved,
                                                   transaction, 
                                                   services);
    }


    @Override
    public Contract setTarget(KeYJavaType newKJT,
            IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   newKJT,
                                                   (IProgramMethod) newPM,
                                                   specifiedIn,
                                                   modality,
                                                   originalPres,
                                                   originalMby,
                                                   originalPosts,
                                                   originalAxioms,
                                                   originalMods,
                                                   originalDeps,
                                                   hasRealModifiesClause,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalAtPreVars,
                                                   globalDefs,
                                                   id,
                                                   toBeSaved && newKJT.equals(kjt),
                                                   transaction, services);
    }


    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, kjt, pm, specifiedIn);
    }


    @Override
    public boolean hasResultVar() {
       return originalResultVar != null;
    }


    @Override
    public boolean hasSelfVar() {
       return originalSelfVar != null;
    }


    @Override
    public KeYJavaType getSpecifiedIn() {
	    return specifiedIn;
    }


    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, ProgramVariable> atPreVars =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        for (LocationVariable h: originalAtPreVars.keySet()) {
            atPreVars.put(h, originalAtPreVars.get(h));
        }
        return new OriginalVariables(originalSelfVar, originalResultVar,
                                     originalExcVar, atPreVars, originalParamVars);
    }
}