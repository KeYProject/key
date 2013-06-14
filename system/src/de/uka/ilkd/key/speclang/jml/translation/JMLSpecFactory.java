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

package de.uka.ilkd.key.speclang.jml.translation;

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassAxiom;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassInv;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLDepends;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLInitially;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLRepresents;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;



/**
 * A factory for creating class invariants and operation contracts
 * from textual JML specifications. This is the public interface to the 
 * jml.translation package.
 */
public class JMLSpecFactory {

    private static final de.uka.ilkd.key.logic.TermBuilder TB = TermBuilder.DF;
    private final de.uka.ilkd.key.java.Services services;
    private final ContractFactory cf;
    private int invCounter;
    /**
     * Used to check that there is only one represents clause per type and
     * field.
     */
    private Set<Pair<KeYJavaType, IObserverFunction>> modelFields;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    public JMLSpecFactory(Services services) {
        assert services != null;
        this.services = services;
        cf = new ContractFactory(services);
        modelFields = new HashSet<Pair<KeYJavaType, IObserverFunction>>();
    }



    //-------------------------------------------------------------------------
    //internal classes
    //-------------------------------------------------------------------------
    private class ContractClauses {

        public Map<LocationVariable,Term> requires = new LinkedHashMap<LocationVariable,Term>();
        public Term measuredBy;
        public Map<LocationVariable,Term> assignables = new LinkedHashMap<LocationVariable,Term>();
        public Term accessible;
        public Map<LocationVariable,Term> ensures = new LinkedHashMap<LocationVariable,Term>();
        public Term signals;
        public Term signalsOnly;
        public Term diverges;
        public Map<Label, Term> breaks;
        public Map<Label, Term> continues;
        public Term returns;
        public boolean strictlyPure;
    }

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private String getDefaultInvName(String name,
                                     KeYJavaType kjt) {
        if (name == null) {
            return "JML class invariant nr " + invCounter++ + " in "
                   + kjt.getName();
        } else {
            return "JML class invariant \"" + name + "\" in " + kjt.getName()
                   + " (nr " + invCounter++ + ")";
        }
    }


    private String getInicName() {
        return "JML initially clause";
    }


    private String getContractName(IProgramMethod programMethod,
                                   Behavior behavior) {
        return "JML " + behavior.toString() + "operation contract";
    }


    /**
     * Collects local variables of the passed statement that are visible for 
     * the passed loop. Returns null if the loop has not been found.
     */
    private ImmutableList<ProgramVariable> collectLocalVariables(
            StatementContainer sc,
            LoopStatement loop) {
        ImmutableList<ProgramVariable> result =
                ImmutableSLList.<ProgramVariable>nil();
        for (int i = 0, m = sc.getStatementCount(); i < m; i++) {
            Statement s = sc.getStatementAt(i);

            if (s instanceof For) {
                ImmutableArray<VariableSpecification> avs =
                        ((For) s).getVariablesInScope();
                for (int j = 0, n = avs.size(); j < n; j++) {
                    VariableSpecification vs = avs.get(j);
                    ProgramVariable pv =
                            (ProgramVariable) vs.getProgramVariable();
                    result = result.prepend(pv);
                }
            }

            if (s == loop) {
                return result;
            } else if (s instanceof LocalVariableDeclaration) {
                ImmutableArray<VariableSpecification> vars =
                        ((LocalVariableDeclaration) s).getVariables();
                for (int j = 0, n = vars.size(); j < n; j++) {
                    ProgramVariable pv =
                            (ProgramVariable) vars.get(j).getProgramVariable();
                    result = result.prepend(pv);
                }
            } else if (s instanceof StatementContainer) {
                ImmutableList<ProgramVariable> lpv =
                        collectLocalVariables((StatementContainer) s, loop);
                if (lpv != null) {
                    result = result.prepend(lpv);
                    return result;
                }
            } else if (s instanceof BranchStatement) {
                BranchStatement bs = (BranchStatement) s;
                for (int j = 0, n = bs.getBranchCount(); j < n; j++) {
                    ImmutableList<ProgramVariable> lpv =
                            collectLocalVariables(bs.getBranchAt(j), loop);
                    if (lpv != null) {
                        result = result.prepend(lpv);
                        return result;
                    }
                }
            }
        }
        return null;
    }


    private VisibilityModifier getVisibility(
            TextualJMLConstruct textualConstruct) {
        for (String mod : textualConstruct.getMods()) {
            if (mod.equals("private")) {
                return new Private();
            } else if (mod.equals("protected")) {
                return new Protected();
            } else if (mod.equals("public")) {
                return new Public();
            }
        }
        return null;
    }

    /* Create variables for self, parameters, result, exception,
     * and the map for atPre-Functions
     */

    private ProgramVariableCollection createProgramVaribales(IProgramMethod pm) {
        ProgramVariableCollection progVar = new ProgramVariableCollection();
        progVar.selfVar = TB.selfVar(services, pm, pm.getContainerType(), false);
        progVar.paramVars = TB.paramVars(services, pm, false);
        progVar.resultVar = TB.resultVar(services, pm, false);
        progVar.excVar = TB.excVar(services, pm, false);

        progVar.atPreVars = new LinkedHashMap<LocationVariable,LocationVariable>();
        progVar.atPres = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
           LocationVariable lv = TB.heapAtPreVar(services, h+"AtPre", h.sort(), false);
           progVar.atPreVars.put(h, lv);
           progVar.atPres.put(h, TB.var(lv));
        }     
        return progVar;
    }


    private ContractClauses translateJMLClauses(IProgramMethod pm,
                                                TextualJMLSpecCase textualSpecCase,
                                                ProgramVariableCollection progVars,
                                                Behavior originalBehavior)
            throws SLTranslationException {
        ContractClauses clauses = new ContractClauses();
        final LocationVariable savedHeap = services.getTypeConverter().getHeapLDT().getSavedHeap();
        clauses.measuredBy =
                translateMeasuredBy(pm, progVars.selfVar,
                                    progVars.paramVars,
                                    textualSpecCase.getMeasuredBy());
        clauses.strictlyPure =
                translateStrictlyPure(pm, progVars.selfVar,
                        progVars.paramVars,
                        textualSpecCase.getAssignable());
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
           if(heap == savedHeap && textualSpecCase.getAssignable(heap.name().toString()).isEmpty()) {
             clauses.assignables.put(heap, null);
           } else if (clauses.strictlyPure) {
               final ImmutableList<PositionedString> assignableNothing = ImmutableSLList.<PositionedString>nil().append(new PositionedString("assignable \\nothing;"));
               clauses.assignables.put(heap, translateAssignable(pm, progVars.selfVar,
                       progVars.paramVars,assignableNothing));
           }else{
             clauses.assignables.put(heap, translateAssignable(pm, progVars.selfVar,
                                    progVars.paramVars,
                                    textualSpecCase.getAssignable(heap.name().toString())));
           }

           if(heap == savedHeap && textualSpecCase.getRequires(heap.name().toString()).isEmpty()) {
             clauses.requires.put(heap, null);
           }else{
             clauses.requires.put(heap, translateAndClauses(pm, progVars.selfVar, progVars.paramVars,
                                    null, null, progVars.atPres,
                                    textualSpecCase.getRequires(heap.name().toString())));
           }
           if(heap == savedHeap && textualSpecCase.getEnsures(heap.name().toString()).isEmpty()) {
             clauses.ensures.put(heap, null);
           }else{
             clauses.ensures.put(heap, translateEnsures(pm, progVars.selfVar,
                                           progVars.paramVars,
                                           progVars.resultVar, progVars.excVar,
                                           progVars.atPres,
                                           originalBehavior,
                                           textualSpecCase.getEnsures(heap.name().toString())));
          }
        }
        clauses.accessible =
                translateAccessible(pm, progVars.selfVar,
                                    progVars.paramVars,
                                    textualSpecCase.getAccessible());
        clauses.signals = translateSignals(pm, progVars.selfVar,
                                           progVars.paramVars,
                                           progVars.resultVar, progVars.excVar,
                                           progVars.atPres,
                                           originalBehavior,
                                           textualSpecCase.getSignals());
        clauses.signalsOnly =
                translateSignalsOnly(pm, progVars.excVar, originalBehavior,
                                     textualSpecCase.getSignalsOnly());
        clauses.diverges = translateOrClauses(pm, progVars.selfVar,
                                              progVars.paramVars,
                                              textualSpecCase.getDiverges());
        clauses.breaks = translateBreaks(pm, progVars.selfVar,
                progVars.paramVars,
                progVars.resultVar, progVars.excVar,
                progVars.atPres,
                originalBehavior,
                textualSpecCase.getBreaks());
        clauses.continues = translateContinues(pm, progVars.selfVar,
                progVars.paramVars,
                progVars.resultVar, progVars.excVar,
                progVars.atPres,
                originalBehavior,
                textualSpecCase.getContinues());
        clauses.returns = translateReturns(pm, progVars.selfVar,
                progVars.paramVars,
                progVars.resultVar, progVars.excVar,
                progVars.atPres,
                originalBehavior,
                textualSpecCase.getReturns());
        return clauses;
    }


    private ImmutableList<ImmutableList<Term>> translateIndependetClauses(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        if (originalClauses.isEmpty()) {
            return ImmutableSLList.<ImmutableList<Term>>nil();
        } else {
            ImmutableList<ImmutableList<Term>> result =
                    ImmutableSLList.<ImmutableList<Term>>nil();
            for (PositionedString expr : originalClauses) {
                ImmutableList<Term> translated =
                        JMLTranslator.translate(
                        expr, pm.getContainerType(), selfVar, paramVars, null,
                        null, null, ImmutableList.class, services);
                result = result.append(translated);
            }
            return result;
        }
    }


    /**
     * Clauses are expected to be conjoined in a right-associative way, i.e. A & (B & ( C (...& N))).
     * When using auto induction with lemmas, then A will be used as a lemma for B, 
     * A & B will be used as a lemma for C and so on. This mimics the Isabelle-style of proving.
     */
    private Term translateAndClauses(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable, Term> atPres,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        //The array is used to invert the order in which the elements are read.
        PositionedString[] array = new PositionedString[originalClauses.size()]; 
        originalClauses.toArray(array);

        Term result = TB.tt();
        for (int i=array.length-1; i>=0 ; i--) {
            Term translated =
                    JMLTranslator.translate(array[i], pm.getContainerType(),
                                            selfVar, paramVars, resultVar,
                                            excVar, atPres,
                                            Term.class, services);
            result = TB.and(TB.convertToFormula(translated,services), result);
        }
        return result;
    }


    private Term translateOrClauses(IProgramMethod pm,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        Term result = TB.ff();
        for (PositionedString expr : originalClauses) {
            Term translated =
                    JMLTranslator.translate(expr, pm.getContainerType(),
                                            selfVar,
                                            paramVars, null, null, null,
                                            Term.class, services);
            result = TB.or(result, TB.convertToFormula(translated,services));
        }
        return result;
    }


    private Term translateUnionClauses(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        Term result = TB.empty(services);
        for (PositionedString expr : originalClauses) {
            Term translated =
                    JMLTranslator.translate(expr, pm.getContainerType(),
                                            selfVar,
                                            paramVars, null, null, null,
                                            Term.class,
                                            services);
            
            // less than nothing is marked by some special term;
            if(translated == TB.strictlyNothing()) {
                if(originalClauses.size() > 1) {
                    throw new SLTranslationException(
                            "\"assignable \\less_than_nothing\" does not go with other " +
                            "assignable clauses (even if they declare the same).",
                            expr.fileName, expr.pos);
                }
                return TB.empty(services);
            }
            
            result = TB.union(services, result, translated);
        }
        
        return result;
    }
    
    private ImmutableList<Term> translateListUnionClauses(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (PositionedString expr : originalClauses) {
            ImmutableList<Term> translated =
                    JMLTranslator.translate(expr, pm.getContainerType(),
                                            selfVar, paramVars, null,
                                            null, null,
                                            ImmutableList.class, services);
            result  = result.append(translated);
        }
        return result;
    }


    private Map<Label, Term> translateBreaks(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable,Term> atPres,
            Behavior originalBehavior,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        PositionedString[] array = new PositionedString[originalClauses.size()];
        originalClauses.toArray(array);
        Map<Label, Term> result = new HashMap<Label, Term>();
        for (int i = array.length - 1; i >= 0; i--) {
            Pair<Label, Term> translation =
                    JMLTranslator.translate(array[i], pm.getContainerType(),
                            selfVar, paramVars, resultVar,
                            excVar, atPres,
                            Pair.class, services);
            result.put(translation.first, translation.second);
        }
        return result;
    }


    private Map<Label, Term> translateContinues(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable,Term> atPres,
            Behavior originalBehavior,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        PositionedString[] array = new PositionedString[originalClauses.size()];
        originalClauses.toArray(array);
        Map<Label, Term> result = new HashMap<Label, Term>();
        for (int i = array.length - 1; i >= 0; i--) {
            Pair<Label, Term> translation =
                    JMLTranslator.translate(array[i], pm.getContainerType(),
                            selfVar, paramVars, resultVar,
                            excVar, atPres,
                            Pair.class, services);
            result.put(translation.first, translation.second);
        }
        return result;
    }


    private Term translateReturns(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable,Term> atPres,
            Behavior originalBehavior,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        if (originalBehavior == Behavior.NORMAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return TB.ff();
        } else {
            return translateAndClauses(pm, selfVar, paramVars, resultVar,
                    excVar, atPres,
                    originalClauses);
        }
    }


    private Term translateSignals(
            IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable,Term> atPres,
            Behavior originalBehavior,
            ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        if (originalBehavior == Behavior.NORMAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return TB.ff();
        } else {
            return translateAndClauses(pm, selfVar, paramVars, resultVar,
                                       excVar, atPres,
                                       originalClauses);
        }
    }


    private Term translateSignalsOnly(IProgramMethod pm,
                                      ProgramVariable excVar,
                                      Behavior originalBehavior,
                                      ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        return translateSignals(pm, null, null, null, excVar, null,
                                originalBehavior, originalClauses);
    }


    private Term translateEnsures(IProgramMethod pm,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars,
                                  ProgramVariable resultVar,
                                  ProgramVariable excVar,
                                  Map<LocationVariable,Term> atPres,
                                  Behavior originalBehavior,
                                  ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        if (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return TB.ff();
        } else {
            return translateAndClauses(pm, selfVar, paramVars, resultVar,
                                       excVar, atPres,
                                       originalClauses);
        }
    }


    private Term translateAccessible(IProgramMethod pm,
                                     ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars,
                                     ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {
        if (originalClauses.isEmpty()) {
            return TB.allLocs(services);
        } else {
            return translateUnionClauses(pm, selfVar, paramVars, originalClauses);
        }
    }


    private Term translateAssignable(IProgramMethod pm,
                                     ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars,
                                     ImmutableList<PositionedString> originalClauses)
            throws SLTranslationException {

        if (originalClauses.isEmpty()) {
            return TB.allLocs(services);
        } else {
            return translateUnionClauses(pm, selfVar, paramVars,
                                         originalClauses);
        }
    }
    
    private boolean translateStrictlyPure(IProgramMethod pm,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ImmutableList<PositionedString> assignableClauses)
                    throws SLTranslationException {
        
        for (PositionedString expr : assignableClauses) {
            Term translated =
                    JMLTranslator.translate(expr, pm.getContainerType(),
                                            selfVar,
                                            paramVars, null, null, null,
                                            Term.class,
                                            services);
            
            // less than nothing is marked by some special term;
            if(translated == TB.strictlyNothing()) {
                return true;
            }
        }
        
        return false;
    }



    private Term translateMeasuredBy(IProgramMethod pm,
                                     ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars,
                                     ImmutableList<PositionedString> originalMeasuredBy)
            throws SLTranslationException {

        Term measuredBy;
        if (originalMeasuredBy.isEmpty()) {
            measuredBy = null;
        } else {
            measuredBy = TB.zero(services);
            for (PositionedString expr : originalMeasuredBy) {
                Term translated = JMLTranslator.translate(expr,
                                                          pm.getContainerType(),
                                                          selfVar, paramVars,
                                                          null, null, null,
                                                          Term.class,
                                                          services);
                measuredBy = TB.add(services, measuredBy, translated);
            }
        }
        return measuredBy;
    }


    private String generateName(IProgramMethod pm,
                                TextualJMLSpecCase textualSpecCase,
                                Behavior originalBehavior) {
        String customName = textualSpecCase.getName();
        String name = ((!(customName == null) && customName.length() > 0)
                       ? customName
                       : getContractName(pm, originalBehavior));
        return name;
    }


    private Map<LocationVariable,Term> generatePostCondition(ProgramVariableCollection progVars,
                                       ContractClauses clauses,
                                       Behavior originalBehavior) {
        Map<LocationVariable,Term> result = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
          if(clauses.ensures.get(heap) != null) {
            Term excNull = TB.equals(TB.var(progVars.excVar), TB.NULL(services));
            Term post1 = (originalBehavior == Behavior.NORMAL_BEHAVIOR
                      ? TB.convertToFormula(clauses.ensures.get(heap),services)
                      : TB.imp(excNull, TB.convertToFormula(clauses.ensures.get(heap),services)));
            Term post2 = (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR
                      ? TB.and(TB.convertToFormula(clauses.signals,services), TB.convertToFormula(clauses.signalsOnly,services)) 
                      : TB.imp(TB.not(excNull),TB.and(TB.convertToFormula(clauses.signals,services), TB.convertToFormula(clauses.signalsOnly,services))));
            result.put(heap, heap == services.getTypeConverter().getHeapLDT().getHeap() ? TB.and(post1, post2) : post1);
          }
        }
        return result;
    }


    /**
     * Generate functional operation contracts.
     * 
     * @param name  base name of the contract (does not have to be unique)
     * @param pm    the IProgramMethod to which the contract belongs
     * @param progVars  pre-generated collection of variables for the receiver
     *          object, operation parameters, operation result, thrown
     *          exception and the pre-heap
     * @param clauses   pre-translated JML clauses
     * @param post  pre-generated post condition
     * @return      operation contracts including new functional operation
     *          contracts
     */
    private ImmutableSet<Contract> createFunctionalOperationContracts(
            String name,
            IProgramMethod pm,
            ProgramVariableCollection progVars,
            ContractClauses clauses,
            Map<LocationVariable,Term> posts) {
        ImmutableSet<Contract> result = DefaultImmutableSet.<Contract>nil();
        Map<LocationVariable,Term> pres = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
           if(clauses.requires.get(heap) != null) {
             final Term pre = TB.convertToFormula(clauses.requires.get(heap), services);
             pres.put(heap, pre);
           }
        }
        if (clauses.diverges.equals(TB.ff())) {
            FunctionalOperationContract contract = cf.func(
                    name, pm, true, pres,
                    clauses.measuredBy, posts, clauses.assignables, 
                    !clauses.strictlyPure, progVars);
            result = result.add(contract);
        } else if (clauses.diverges.equals(TB.tt())) {
            FunctionalOperationContract contract = cf.func(
                    name, pm, false, pres,
                    clauses.measuredBy, posts, clauses.assignables, !clauses.strictlyPure, progVars);
            result = result.add(contract);
        } else {
            for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
              if(clauses.requires.get(heap) != null) {
                final Term pre = TB.convertToFormula(clauses.requires.get(heap), services);
                pres.put(heap, TB.and(pres.get(heap), TB.not(TB.convertToFormula(clauses.diverges,services))));
              }
            }
            FunctionalOperationContract contract1 = cf.func(
                    name, pm, true,
                    pres,
                    clauses.measuredBy, posts, clauses.assignables,
                    !clauses.strictlyPure, progVars);
            FunctionalOperationContract contract2 =
                    cf.func(name, pm, false, clauses.requires, clauses.measuredBy, posts,
                        clauses.assignables, !clauses.strictlyPure, progVars);
            result = result.add(contract1).add(contract2);
        }
        return result;
    }


    /**
     * Generate dependency operation contract out of the JML accessible clause.
     * 
     * @param pm    the IProgramMethod to which the contract belongs
     * @param progVars  collection of variables for the receiver object,
     *          operation parameters, operation result, thrown exception
     *          and the pre-heap
     * @param clauses   pre-translated JML clauses
     * @return      operation contracts including a new dependency contract
     */
    private ImmutableSet<Contract> createDependencyOperationContract(
            IProgramMethod pm,
            ProgramVariableCollection progVars,
            ContractClauses clauses) {
        ImmutableSet<Contract> result = DefaultImmutableSet.<Contract>nil();
        if (!clauses.accessible.equalsModRenaming(TB.allLocs(services))) {
            assert (progVars.selfVar == null) == pm.isStatic();
            final Contract depContract = cf.dep(
                    pm.getContainerType(), pm, pm.getContainerType(),
                    TB.convertToFormula(clauses.requires.get(services.getTypeConverter().getHeapLDT().getHeap()),services), clauses.measuredBy,
                    clauses.accessible, progVars.selfVar,
                    progVars.paramVars);
            result = result.add(depContract);
        }
        return result;
    }


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    public ClassInvariant createJMLClassInvariant(KeYJavaType kjt,
                                                  VisibilityModifier visibility,
                                                  boolean isStatic,
                                                  PositionedString originalInv)
            throws SLTranslationException {
        assert kjt != null;
        assert originalInv != null;

        //create variable for self
        ProgramVariable selfVar = isStatic? null: TB.selfVar(services, kjt, false);

        //translateToTerm expression
        Term inv = TB.convertToFormula(JMLTranslator.translate(originalInv, kjt, selfVar, null, null,
                                           null, null, Term.class,
                                           services),services);
        //create invariant
        String name = getDefaultInvName(null, kjt);
        return new ClassInvariantImpl(name,
                                      name,
                                      kjt,
                                      visibility,
                                      inv,
                                      selfVar);
    }


    public ClassInvariant createJMLClassInvariant(
            KeYJavaType kjt,
            TextualJMLClassInv textualInv)
            throws SLTranslationException {
        // check whether the invariant is static
        final ImmutableList<String> mods = textualInv.getMods();
        final boolean isStatic = (mods.contains("static") || // modifier "static" 
                // in an interface "static" is the default (see Sect. 2.5 of the reference manual)
                (services.getJavaInfo().isInterface(kjt) && !mods.contains("instance")));
        
        //create variable for self
        ProgramVariable selfVar = isStatic? null: TB.selfVar(services, kjt, false);

        //translateToTerm expression
        Term inv = TB.convertToFormula(JMLTranslator.translate(textualInv.getInv(), kjt, selfVar,
                                           null, null, null, null,
                                           Term.class, services),services);
        //create invariant
        String name = getDefaultInvName(null, kjt);
        String display = getDefaultInvName(textualInv.getName(), kjt);
        return new ClassInvariantImpl(name,
                                      display,
                                      kjt,
                                      getVisibility(textualInv),
                                      inv,
                                      selfVar);
    }


    public InitiallyClause createJMLInitiallyClause(KeYJavaType kjt,
                                                    VisibilityModifier visibility,
                                                    PositionedString original)
            throws SLTranslationException {
        assert kjt != null;
        assert original != null;



        //create variable for self
        ProgramVariable selfVar = TB.selfVar(services, kjt, false);

        //translateToTerm expression
        Term inv = TB.convertToFormula(JMLTranslator.translate(original, kjt, selfVar, null, null,
                                           null, null, Term.class,
                                           services),services);
        //create invariant
        String name = getInicName();
        InitiallyClauseImpl res = new InitiallyClauseImpl(name,
                                                          name,
                                                          kjt,
                                                          new Public(),
                                                          inv,
                                                          selfVar, original);
        return res;

    }


    public InitiallyClause createJMLInitiallyClause(KeYJavaType kjt,
                                                    TextualJMLInitially textualInv)
            throws SLTranslationException {
        return createJMLInitiallyClause(kjt,
                                        getVisibility(textualInv),
                                        textualInv.getInv());
    }


    @SuppressWarnings("unchecked")
    public ClassAxiom createJMLRepresents(KeYJavaType kjt,
                                          VisibilityModifier visibility,
                                          PositionedString originalRep,
                                          boolean isStatic)
            throws SLTranslationException {
        assert kjt != null;
        assert originalRep != null;

        //create variable for self
        final ProgramVariable selfVar =
                isStatic ? null : TB.selfVar(services, kjt, false);

        //translateToTerm expression
        final Pair<IObserverFunction, Term> rep =
                JMLTranslator.translate(originalRep, kjt, selfVar, null, null,
                                        null, null, Pair.class, services);
        // represents clauses must be unique per type
        for (Pair<KeYJavaType, IObserverFunction> p : modelFields) {
            if (p.first.equals(kjt) && p.second.equals(rep.first)) {
                throw new SLTranslationException(
                        "JML represents clauses must occur uniquely per type and target.",
                        originalRep.fileName,
                        originalRep.pos);
            }
        }
        modelFields.add(new Pair<KeYJavaType, IObserverFunction>(kjt, rep.first));
        Term repFormula = TB.convertToFormula(rep.second, services);
        //create class axiom
        return new RepresentsAxiom("JML represents clause for "
                                   + rep.first.name().toString(),
                                   rep.first,
                                   kjt,
                                   visibility,
                                   repFormula,
                                   selfVar);
    }


    @SuppressWarnings("unchecked")
    public ClassAxiom createJMLRepresents(KeYJavaType kjt,
                                          TextualJMLRepresents textualRep)
            throws SLTranslationException {
        boolean isStatic = textualRep.getMods().contains("static");
        //create variable for self
        final ProgramVariable selfVar =
                isStatic ? null : TB.selfVar(services, kjt, false);

        //translateToTerm expression
        final PositionedString clause = textualRep.getRepresents();
        final Pair<IObserverFunction, Term> rep =
                JMLTranslator.translate(clause, kjt, selfVar, null, null, null,
                                        null, Pair.class, services);
        //check whether there already is a represents clause
        if (!modelFields.add(new Pair<KeYJavaType, IObserverFunction>(kjt,
                                                                     rep.first))) {
            throw new SLWarningException("JML represents clauses must occur uniquely per type and target."
                                         + "\nAll but one are ignored.",
                                         clause.fileName, clause.pos);
        }
        //create class axiom
        String name = "JML represents clause for "
                      + rep.first.name().toString();
        String displayName = textualRep.getName() == null ? name
                             : "JML represents clause \"" + textualRep.getName()
                               + "\" for " + rep.first.name();
        Term repFormula = TB.convertToFormula(rep.second, services);
        return new RepresentsAxiom(name, displayName,
                                   rep.first,
                                   kjt,
                                   getVisibility(textualRep),
                                   repFormula,
                                   selfVar);
    }


    /**
     * Creates a class axiom from a textual JML representation.
     * As JML axioms are always without modifiers, they are implicitly non-static and public.
     * @param kjt the type where the axiom is declared
     * @param textual textual representation
     * @throws SLTranslationException
     */
    public ClassAxiom createJMLClassAxiom(KeYJavaType kjt,
                                          TextualJMLClassAxiom textual)
            throws SLTranslationException {
        PositionedString originalRep = textual.getAxiom();
        assert kjt != null;
        assert originalRep != null;

        //create variable for self
        final ProgramVariable selfVar = TB.selfVar(services, kjt, false);

        //translate expression
        final Term ax = TB.convertToFormula(
                JMLTranslator.translate(originalRep, kjt, selfVar, null, null,
                                        null, null, Term.class, services),services);

        //create class axiom
        String name = "class axiom in " + kjt.getFullName();
        String displayName = textual.getName() == null ? name
                             : "class axiom \"" + textual.getName() + "\" in "
                               + kjt.getFullName();
        return new ClassAxiomImpl(name, displayName, kjt,
                                  new Public(), ax, selfVar);
    }


    @SuppressWarnings("unchecked")
    public Contract createJMLDependencyContract(KeYJavaType kjt,
                                                PositionedString originalDep)
            throws SLTranslationException {
        assert kjt != null;
        assert originalDep != null;

        //create variable for self
        ProgramVariable selfVar = TB.selfVar(services, kjt, false);

        //translateToTerm expression
        Triple<IObserverFunction, Term, Term> dep =
                JMLTranslator.translate(originalDep, kjt, selfVar, null, null,
                                        null, null, Triple.class, services);
        assert dep.first.arity() <= 2;
        return cf.dep(kjt, dep, dep.first.isStatic() ? null : selfVar);
    }


    public Contract createJMLDependencyContract(KeYJavaType kjt,
                                                TextualJMLDepends textualDep)
            throws SLTranslationException {
        return createJMLDependencyContract(kjt, textualDep.getDepends());
    }


    /**
     * Creates operation contracts out of the passed JML specification.
     */
    public ImmutableSet<Contract> createJMLOperationContracts(IProgramMethod pm,
                                                              TextualJMLSpecCase textualSpecCase)
            throws SLTranslationException {
        assert pm != null;
        assert textualSpecCase != null;

        Behavior originalBehavior = textualSpecCase.getBehavior();
        String name = generateName(pm, textualSpecCase, originalBehavior);

        // prepare program variables, translateToTerm JML clauses and generate post
        // condition
        ProgramVariableCollection progVars = createProgramVaribales(pm);
        ContractClauses clauses =
                translateJMLClauses(pm, textualSpecCase,
                                    progVars, originalBehavior);
        Map<LocationVariable,Term> posts = generatePostCondition(progVars, clauses, originalBehavior);

        // create contracts
        ImmutableSet<Contract> result = DefaultImmutableSet.<Contract>nil();
        result = result.union(createFunctionalOperationContracts(name, pm,
                                                                 progVars,
                                                                 clauses, posts));
        result = result.union(createDependencyOperationContract(pm, progVars,
                                                                clauses));

        return result;
    }
    
    public ImmutableSet<BlockContract> createJMLBlockContracts(final IProgramMethod method,
                                                               final List<Label> labels,
                                                               final StatementBlock block,
                                                               final TextualJMLSpecCase specificationCase)
            throws SLTranslationException
    {
        final Behavior behavior = specificationCase.getBehavior();
        final BlockContract.Variables variables = BlockContract.Variables.create(block, labels, method, services);
        final ProgramVariableCollection programVariables = createProgramVariables(method, block, variables);
        final ContractClauses clauses = translateJMLClauses(method, specificationCase, programVariables, behavior);
        return new SimpleBlockContract.Creator(
            block, labels, method, behavior, variables, clauses.requires, clauses.ensures, clauses.breaks, clauses.continues,
            clauses.returns, clauses.signals, clauses.signalsOnly, clauses.diverges, clauses.assignables, !clauses.strictlyPure, services
        ).create();
    }

    private ProgramVariableCollection createProgramVariables(final IProgramMethod method, final StatementBlock block, final BlockContract.Variables variables)
    {
        final Map<LocationVariable, LocationVariable> remembranceVariables = variables.combineRemembranceVariables();
        return new ProgramVariableCollection(
            variables.self, collectParameters(method).append(collectLocalVariablesVisibleTo(block, method)),
            variables.result, variables.exception, remembranceVariables, termify(remembranceVariables)
        );
    }

    private Map<LocationVariable, Term> termify(final Map<LocationVariable, LocationVariable> remembranceVariables)
    {
        final Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : remembranceVariables.entrySet()) {
            result.put(remembranceVariable.getKey(), TB.var(remembranceVariable.getValue()));
        }
        return result;
    }

    // TODO Move to IProgramMethod interface and its implementations.
    private ImmutableList<ProgramVariable> collectParameters(final IProgramMethod method) {
        ImmutableList<ProgramVariable> result = ImmutableSLList.nil();
        final int parameterCount = method.getParameterDeclarationCount();
        for (int i = parameterCount - 1; i >= 0; i--) {
            ParameterDeclaration parameter = method.getParameterDeclarationAt(i);
            result = result.prepend((ProgramVariable) parameter.getVariableSpecification().getProgramVariable());
        }
        return result;
    }

    protected ImmutableList<ProgramVariable> collectLocalVariablesVisibleTo(final Statement statement, final IProgramMethod method)
    {
        return collectLocalVariablesVisibleTo(statement, method.getBody());
    }

    private ImmutableList<ProgramVariable> collectLocalVariablesVisibleTo(final Statement statement, final StatementContainer container)
    {
        ImmutableList<ProgramVariable> result = ImmutableSLList.nil();
        final int statementCount = container.getStatementCount();
        for (int i = 0; i < statementCount; i++) {
            final Statement s = container.getStatementAt(i);
            if (s instanceof For) {
                final ImmutableArray<VariableSpecification> variables = ((For) s).getVariablesInScope();
                for (int j = 0; j < variables.size(); j++) {
                    result = result.prepend((ProgramVariable) variables.get(j).getProgramVariable());
                }
            }
            if (s == statement) {
                return result;
            }
            else if (s instanceof LocalVariableDeclaration) {
                final ImmutableArray<VariableSpecification> variables = ((LocalVariableDeclaration) s).getVariables();
                for (int j = 0; j < variables.size(); j++) {
                    result = result.prepend((ProgramVariable) variables.get(j).getProgramVariable());
                }
            }
            else if (s instanceof StatementContainer) {
                final ImmutableList<ProgramVariable> visibleLocalVariables
                        = collectLocalVariablesVisibleTo(statement, (StatementContainer) s);
                if (visibleLocalVariables != null) {
                    result = result.prepend(visibleLocalVariables);
                    return result;
                }
            }
            else if (s instanceof BranchStatement) {
                final BranchStatement branch = (BranchStatement) s;
                final int branchCount = branch.getBranchCount();
                for (int j = 0; j < branchCount; j++) {
                    final ImmutableList<ProgramVariable> visibleLocalVariables
                            = collectLocalVariablesVisibleTo(statement, branch.getBranchAt(j));
                    if (visibleLocalVariables != null) {
                        result = result.prepend(visibleLocalVariables);
                        return result;
                    }
                }
            }
        }
        return null;
    }

    public LoopInvariant createJMLLoopInvariant(
            IProgramMethod pm,
            LoopStatement loop,
            Map<String,ImmutableList<PositionedString>> originalInvariants,
            Map<String,ImmutableList<PositionedString>> originalAssignables,
            PositionedString originalVariant)
            throws SLTranslationException {
        assert pm != null;
        assert loop != null;
        assert originalInvariants != null;
        assert originalAssignables != null;

        //create variables for self, parameters, other relevant local variables 
        //(disguised as parameters to the translator) and the map for 
        //atPre-Functions
        ProgramVariable selfVar =
                TB.selfVar(services, pm, pm.getContainerType(), false);
        ImmutableList<ProgramVariable> paramVars =
                ImmutableSLList.<ProgramVariable>nil();
        int numParams = pm.getParameterDeclarationCount();
        for (int i = numParams - 1; i >= 0; i--) {
            ParameterDeclaration pd = pm.getParameterDeclarationAt(i);
            paramVars =
                    paramVars.prepend(
                    (ProgramVariable) pd.getVariableSpecification().getProgramVariable());
        }

        ImmutableList<ProgramVariable> localVars =
                collectLocalVariables(pm.getBody(), loop);
        paramVars = paramVars.append(localVars);

        Map<LocationVariable,Term> atPres = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
          atPres.put(heap, TB.var(TB.heapAtPreVar(services, heap+"AtPre", heap.sort(), false)));        
        }

        //translateToTerm invariant
        Map<LocationVariable,Term> invariants = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
          Term invariant;
          ImmutableList<PositionedString> originalInvariant = originalInvariants.get(heap.name().toString());
          if (originalInvariant.isEmpty()) {
            invariant = null;
          } else {
            invariant = TB.tt();
            for (PositionedString expr : originalInvariant) {
                Term translated =
                        JMLTranslator.translate(expr, pm.getContainerType(),
                                                selfVar, paramVars, null,
                                                null, atPres,
                                                Term.class, services);
                invariant = TB.and(invariant, TB.convertToFormula(translated,services));
            }
          }          
          invariants.put(heap, invariant);
        }
        //translateToTerm assignable
        Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();
        for(String h : originalAssignables.keySet()) {
           Term a = null;
           ImmutableList<PositionedString> as = originalAssignables.get(h);
           if(as.isEmpty()) {
             a = TB.allLocs(services);
           }else{
             a = TB.empty(services);
             for (PositionedString expr : as) {
                Term translated =
                        JMLTranslator.translate(expr, pm.getContainerType(),
                                                selfVar, paramVars, null,
                                                null, null, Term.class,
                                                services);
                a = TB.union(services, a, translated);
             }
           }
           
           mods.put(services.getTypeConverter().getHeapLDT().getHeapForName(new Name(h)), a);
        }

        //translateToTerm variant
        Term variant;
        if (originalVariant == null) {
            variant = null;
        } else {
            Term translated =
                    JMLTranslator.translate(originalVariant,
                                            pm.getContainerType(), selfVar,
                                            paramVars, null, null, atPres, Term.class, services);
            variant = translated;
        }
        //create loop invariant annotation
        Term selfTerm = selfVar == null ? null : TB.var(selfVar);
        return new LoopInvariantImpl(loop,
                                     invariants,
                                     mods,
                                     variant,
                                     selfTerm,
                                     atPres);
    }


    public LoopInvariant createJMLLoopInvariant(
            IProgramMethod pm,
            LoopStatement loop,
            TextualJMLLoopSpec textualLoopSpec)
            throws SLTranslationException {
        return createJMLLoopInvariant(pm,
                                      loop,
                                      textualLoopSpec.getInvariants(),
                                      textualLoopSpec.getAssignables(),
                                      textualLoopSpec.getVariant());
    }


    /**
     * Translate initially clause to a contract for the given constructor.
     * Exception is thrown if the methods passed is not a constructor.
     * For an initially clause <tt>ini</tt> the resulting contract looks like:<br>
     * <tt>requires true;<br>ensures ini;<br>signals (Exception) ini;<br>diverges true;</tt>
     * @param pm constructor
     */
    public FunctionalOperationContract initiallyClauseToContract(
            InitiallyClause ini,
            IProgramMethod pm)
            throws SLTranslationException {
        //if (! pm.isConstructor()) throw new SLTranslationException("Initially clauses only apply to constructors, not to method "+pm);
        final ImmutableList<String> mods = ImmutableSLList.<String>nil().append(
                "private");
        final TextualJMLSpecCase specCase =
                new TextualJMLSpecCase(mods, Behavior.NONE);
        specCase.addName(new PositionedString(ini.getName()));
        specCase.addRequires(createPrecond(pm, ini.getOriginalSpec()));
        specCase.addEnsures(ini.getOriginalSpec().prepend(
                "\\invariant_for(this) &&"));
        specCase.addSignals(ini.getOriginalSpec().prepend(
                "\\invariant_for(this) &&"));
        specCase.addDiverges(new PositionedString("true"));
        ImmutableSet<Contract> resultList =
                createJMLOperationContracts(pm, specCase);
        assert resultList.size() == 1;
        Contract result = resultList.toArray(new Contract[1])[0];
        assert result instanceof FunctionalOperationContract;
        return ((FunctionalOperationContract) result);
    }


    private ImmutableList<PositionedString> createPrecond(IProgramMethod pm,
                                                          PositionedString originalSpec) {
        ImmutableList<PositionedString> res =
                ImmutableSLList.<PositionedString>nil();
        // TODO: add static invariant
        for (ParameterDeclaration p : pm.getMethodDeclaration().getParameters()) {
            if (!JMLInfoExtractor.parameterIsNullable(pm, p)) {
                res =
                        res.append(
                        JMLSpecExtractor.createNonNullPositionedString(
                        p.getVariableSpecification().getName(),
                        p.getVariableSpecification().getProgramVariable().getKeYJavaType(),
                        false,
                        originalSpec.fileName,
                        originalSpec.pos,
                        services));
            }
        }
        return res;
    }
}
