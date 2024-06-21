/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.translation;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
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
import de.uka.ilkd.key.java.statement.SetStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.HeapLDT.SplitFieldName;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.rule.merge.procedures.ParametricMergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.UnparametricMergeProcedure;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.njml.*;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.mergerule.MergeParamsSpec;

import org.key_project.logic.Name;
import org.key_project.util.collection.*;
import org.key_project.util.collection.Pair;

import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingProperty.RENAMING_PROPERTY;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.DIVERGES;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.SIGNALS;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ENSURES;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.REQUIRES;
import static java.lang.String.format;

/**
 * A factory for creating class invariants and operation contracts from textual JML specifications.
 * This is the public interface to the jml.translation package.
 */
public class JMLSpecFactory {

    public static final String AT_PRE = "AtPre";
    protected final de.uka.ilkd.key.logic.TermBuilder tb;
    protected final de.uka.ilkd.key.java.Services services;
    protected final ContractFactory cf;

    /**
     * Counter for numbering the partial invariant rules. One counter is maintained per type.
     * Otherwise, partial invariant taclets might not be applicable during proof reloading, when
     * additional classes are added.
     */
    private final Map<KeYJavaType, Integer> invCounter = new IdentityHashMap<>();
    /**
     * Used to check that there is only one represents clause per type and field.
     */
    private final Set<Pair<KeYJavaType, IObserverFunction>> modelFields;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------
    public JMLSpecFactory(Services services) {
        if (services == null) {
            throw new AssertionError();
        }
        this.services = services;
        this.tb = services.getTermBuilder();
        cf = new ContractFactory(services);
        modelFields = new LinkedHashSet<>();
    }

    private static Map<LocationVariable, Term> createAtPres(
            final ImmutableList<LocationVariable> paramVars,
            final ImmutableList<LocationVariable> allHeaps, final TermBuilder tb) {
        Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
        for (LocationVariable heap : allHeaps) {
            atPres.put(heap, tb.var(tb.atPreVar(heap.toString(), heap.sort(), false)));
        }
        for (LocationVariable param : paramVars) {
            atPres.put(param, tb.var(tb.atPreVar(param.toString(), param.sort(), false)));
        }
        return atPres;
    }

    private static Map<LocationVariable, Term> translateToTermInvariants(Context context,
            Map<String, ImmutableList<LabeledParserRuleContext>> originalInvariants,
            ImmutableList<LocationVariable> allVars, final ImmutableList<LocationVariable> allHeaps,
            final Map<LocationVariable, Term> atPres, final Services services,
            final TermBuilder tb) {
        Map<LocationVariable, Term> invariants = new LinkedHashMap<>();
        for (LocationVariable heap : allHeaps) {
            Term invariant;
            ImmutableList<LabeledParserRuleContext> originalInvariant =
                originalInvariants.get(heap.name().toString());
            if (originalInvariant == null || originalInvariant.isEmpty()) {
                invariant = null;
            } else {
                invariant = tb.tt();
                for (LabeledParserRuleContext expr : originalInvariant) {
                    Term translated =
                        new JmlIO(services).context(context).parameters(allVars).atPres(atPres)
                                .atBefore(atPres).translateTerm(expr, SpecType.LOOP_INVARIANT);
                    invariant = tb.andSC(invariant, tb.convertToFormula(translated));
                }
            }
            invariants.put(heap, invariant);
        }
        return invariants;
    }

    private static Map<LocationVariable, Term> translateToTermFreeInvariants(Context context,
            Map<String, ImmutableList<LabeledParserRuleContext>> originalFreeInvariants,
            ImmutableList<LocationVariable> allVars, final ImmutableList<LocationVariable> allHeaps,
            final Map<LocationVariable, Term> atPres, final Services services,
            final TermBuilder tb) {
        Map<LocationVariable, Term> freeInvariants = new LinkedHashMap<>();
        for (LocationVariable heap : allHeaps) {
            Term freeInvariant;
            ImmutableList<LabeledParserRuleContext> originalFreeInvariant =
                originalFreeInvariants.get(heap.name().toString());
            if (originalFreeInvariant == null || originalFreeInvariant.isEmpty()) {
                freeInvariant = null;
            } else {
                freeInvariant = tb.tt();
                for (LabeledParserRuleContext expr : originalFreeInvariant) {
                    Term translated = new JmlIO(services).context(context)
                            .parameters(allVars).atPres(atPres).atBefore(atPres)
                            .translateTerm(expr, SpecType.LOOP_INVARIANT_FREE);
                    freeInvariant = tb.andSC(freeInvariant, tb.convertToFormula(translated));
                }
            }
            freeInvariants.put(heap, freeInvariant);
        }
        return freeInvariants;
    }

    private ImmutableSet<Contract> createInformationFlowContracts(ContractClauses clauses,
            IProgramMethod pm, ProgramVariableCollection progVars) {
        LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();

        // create contracts
        ImmutableSet<Contract> symbDatas = DefaultImmutableSet.nil();
        if (clauses.infFlowSpecs != null && !clauses.infFlowSpecs.isEmpty()) {
            if (clauses.diverges.equals(tb.ff())) {
                InformationFlowContract symbData = cf.createInformationFlowContract(
                    pm.getContainerType(), pm, pm.getContainerType(), Modality.JavaModalityKind.DIA,
                    clauses.requires.get(heap), clauses.requiresFree.get(heap), clauses.measuredBy,
                    clauses.assignables.get(heap), !clauses.hasAssignable.get(heap), progVars,
                    clauses.accessibles.get(heap), clauses.infFlowSpecs, false);
                symbDatas = symbDatas.add(symbData);
            } else if (clauses.diverges.equals(tb.tt())) {
                InformationFlowContract symbData = cf.createInformationFlowContract(
                    pm.getContainerType(), pm, pm.getContainerType(), Modality.JavaModalityKind.BOX,
                    clauses.requires.get(heap), clauses.requiresFree.get(heap), clauses.measuredBy,
                    clauses.assignables.get(heap), !clauses.hasAssignable.get(heap), progVars,
                    clauses.accessibles.get(heap), clauses.infFlowSpecs, false);
                symbDatas = symbDatas.add(symbData);
            } else {
                InformationFlowContract symbData1 = cf.createInformationFlowContract(
                    pm.getContainerType(), pm, pm.getContainerType(), Modality.JavaModalityKind.DIA,
                    tb.and(clauses.requires.get(heap), tb.not(clauses.diverges)),
                    clauses.requiresFree.get(heap), clauses.measuredBy,
                    clauses.assignables.get(heap), !clauses.hasAssignable.get(heap), progVars,
                    clauses.accessibles.get(heap), clauses.infFlowSpecs, false);
                InformationFlowContract symbData2 = cf.createInformationFlowContract(
                    pm.getContainerType(), pm, pm.getContainerType(), Modality.JavaModalityKind.BOX,
                    clauses.requires.get(heap), clauses.requiresFree.get(heap), clauses.measuredBy,
                    clauses.assignables.get(heap), !clauses.hasAssignable.get(heap), progVars,
                    clauses.accessibles.get(heap), clauses.infFlowSpecs, false);
                symbDatas = symbDatas.add(symbData1).add(symbData2);
            }
        }
        return symbDatas;
    }

    // -------------------------------------------------------------------------
    // internal classes
    // -------------------------------------------------------------------------
    public static class ContractClauses {
        public ImmutableList<Term> abbreviations = ImmutableSLList.nil();
        public final Map<LocationVariable, Term> requires = new LinkedHashMap<>();
        public final Map<LocationVariable, Term> requiresFree = new LinkedHashMap<>();
        public Term measuredBy;
        public Term decreases;
        /**
         * The name 'assignable' is kept here for legacy reasons.
         * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
         */
        public final Map<LocationVariable, Term> assignables = new LinkedHashMap<>();
        /**
         * The name 'assignable' is kept here for legacy reasons.
         * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
         */
        public final Map<LocationVariable, Term> assignablesFree = new LinkedHashMap<>();
        public final Map<LocationVariable, Term> accessibles = new LinkedHashMap<>();
        public final Map<LocationVariable, Term> ensures = new LinkedHashMap<>();
        public final Map<LocationVariable, Term> ensuresFree = new LinkedHashMap<>();
        public final Map<LocationVariable, Term> axioms = new LinkedHashMap<>();
        public Term signals;
        public Term signalsOnly;
        public Term diverges;
        public Map<Label, Term> breaks;
        public Map<Label, Term> continues;
        public Term returns;
        public final Map<LocationVariable, Boolean> hasAssignable = new LinkedHashMap<>();
        public final Map<LocationVariable, Boolean> hasFreeAssignable = new LinkedHashMap<>();
        public ImmutableList<InfFlowSpec> infFlowSpecs;

        public void clear() {
        }
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    protected String getDefaultInvName(String name, KeYJavaType kjt) {
        if (name == null) {
            int number = invCounter.getOrDefault(kjt, 1);
            invCounter.put(kjt, number + 1);
            return "JML class invariant in " + kjt.getFullName() + " no " + number;
        } else {
            return "JML class invariant \"" + name + "\" in " + kjt.getFullName();
        }
    }

    private String getInicName() {
        return "JML initially clause";
    }

    private String getContractName(IProgramMethod programMethod, Behavior behavior) {
        return "JML " + behavior.toString() + "operation contract";
    }

    /**
     * Collects local variables of the passed statement that are visible for the passed loop.
     * Returns null if the loop has not been found.
     */
    private ImmutableList<LocationVariable> collectLocalVariables(StatementContainer sc,
            LoopStatement loop) {
        ImmutableList<LocationVariable> result = ImmutableSLList.nil();
        for (int i = 0, m = sc.getStatementCount(); i < m; i++) {
            Statement s = sc.getStatementAt(i);

            if (s instanceof For) {
                ImmutableArray<VariableSpecification> avs = ((For) s).getVariablesInScope();
                for (int j = 0, n = avs.size(); j < n; j++) {
                    VariableSpecification vs = avs.get(j);
                    LocationVariable pv = (LocationVariable) vs.getProgramVariable();
                    result = result.prepend(pv);
                }
            }

            if (s == loop) {
                return result;
            } else if (s instanceof LocalVariableDeclaration) {
                ImmutableArray<VariableSpecification> vars =
                    ((LocalVariableDeclaration) s).getVariables();
                for (int j = 0, n = vars.size(); j < n; j++) {
                    LocationVariable pv = (LocationVariable) vars.get(j).getProgramVariable();
                    result = result.prepend(pv);
                }
            } else if (s instanceof StatementContainer) {
                ImmutableList<LocationVariable> lpv =
                    collectLocalVariables((StatementContainer) s, loop);
                if (lpv != null) {
                    result = result.prepend(lpv);
                    return result;
                }
            } else if (s instanceof BranchStatement bs) {
                for (int j = 0, n = bs.getBranchCount(); j < n; j++) {
                    ImmutableList<LocationVariable> lpv =
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

    private VisibilityModifier getVisibility(TextualJMLConstruct textualConstruct) {
        for (JMLModifier modifier : textualConstruct.getModifiers()) {
            if (modifier.equals(JMLModifier.PRIVATE)) {
                return new Private();
            } else if (modifier.equals(JMLModifier.PROTECTED)) {
                return new Protected();
            } else if (modifier.equals(JMLModifier.PUBLIC)) {
                return new Public();
            }
        }
        return null;
    }

    /*
     * Create variables for self, parameters, result, exception, and the map for atPre-Functions
     */

    public ProgramVariableCollection createProgramVariables(IProgramMethod pm) {
        ProgramVariableCollection progVar = new ProgramVariableCollection();
        progVar.selfVar = tb.selfVar(pm, pm.getContainerType(), false);
        progVar.paramVars = tb.paramVars(pm, false);
        progVar.resultVar = tb.resultVar(pm, false);
        progVar.excVar = pm.isModel() ? null : tb.excVar(pm, false);

        progVar.atPreVars = new LinkedHashMap<>();
        progVar.atPres = new LinkedHashMap<>();
        for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            LocationVariable lv = tb.atPreVar(h.toString(), h.sort(), false);
            progVar.atPreVars.put(h, lv);
            progVar.atPres.put(h, tb.var(lv));
        }
        return progVar;
    }

    private static @Nullable SpecMathMode specMathModeFromModifiers(
            ImmutableList<JMLModifier> modifiers) {
        for (var modifier : modifiers) {
            // Consistency: bigint > safe > java
            if (modifier == JMLModifier.SPEC_BIGINT_MATH) {
                return SpecMathMode.BIGINT;
            }
            if (modifier == JMLModifier.SPEC_SAFE_MATH) {
                return SpecMathMode.JAVA;
            }
            if (modifier == JMLModifier.SPEC_JAVA_MATH) {
                return SpecMathMode.JAVA;
            }
        }
        return null;
    }

    private ContractClauses translateJMLClauses(TextualJMLSpecCase textualSpecCase,
            Context outerContext, ProgramVariableCollection progVars, Behavior originalBehavior)
            throws SLTranslationException {
        var context =
            outerContext
                    .orWithSpecMathMode(specMathModeFromModifiers(textualSpecCase.getModifiers()));
        ContractClauses clauses = new ContractClauses();
        final LocationVariable savedHeap = services.getTypeConverter().getHeapLDT().getSavedHeap();

        clauses.abbreviations =
            registerAbbreviationVariables(textualSpecCase, context, progVars, clauses);

        clauses.measuredBy =
            translateMeasuredBy(context, progVars.paramVars, textualSpecCase.getMeasuredBy());

        clauses.decreases = translateDecreases(context, progVars.paramVars, progVars.atPres,
            progVars.atBefores, textualSpecCase.getDecreases());

        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            translateAssignable(context, progVars, heap, savedHeap,
                textualSpecCase.getAssignable(heap.name()),
                textualSpecCase.getAssignableFree(heap.name()), clauses);
            translateRequires(context, progVars, heap, savedHeap,
                textualSpecCase.getRequires(heap.name()),
                textualSpecCase.getRequiresFree(heap.name()), clauses);
            translateEnsures(context, progVars, heap, savedHeap,
                textualSpecCase.getEnsures(heap.name()),
                textualSpecCase.getEnsuresFree(heap.name()), clauses, originalBehavior);
            translateAxioms(context, progVars, heap, textualSpecCase.getAxioms(heap.name()),
                clauses, originalBehavior);
            translateAccessible(context, progVars, heap, progVars.atPreVars.get(heap), savedHeap,
                textualSpecCase.getAccessible(heap.name()),
                textualSpecCase.getAccessible(new Name(heap.name() + AT_PRE)), clauses);
        }
        clauses.signals = translateSignals(context, progVars.paramVars, progVars.resultVar,
            progVars.excVar, progVars.atPres, progVars.atBefores, originalBehavior,
            textualSpecCase.getSignals());
        clauses.signalsOnly = translateSignalsOnly(context, progVars.excVar, originalBehavior,
            textualSpecCase.getSignalsOnly());
        clauses.diverges =
            translateOrClauses(context, progVars.paramVars, textualSpecCase.getDiverges());
        clauses.breaks =
            translateBreaks(context, progVars.paramVars, progVars.resultVar, progVars.excVar,
                progVars.atPres, progVars.atBefores, originalBehavior, textualSpecCase.getBreaks());
        clauses.continues = translateContinues(context, progVars.paramVars, progVars.resultVar,
            progVars.excVar, progVars.atPres, progVars.atBefores, originalBehavior,
            textualSpecCase.getContinues());
        clauses.returns = translateReturns(context, progVars.paramVars, progVars.resultVar,
            progVars.excVar, progVars.atPres, progVars.atBefores, originalBehavior,
            textualSpecCase.getReturns());
        clauses.infFlowSpecs = translateInfFlowSpecClauses(context, progVars.paramVars,
            progVars.resultVar, progVars.excVar, textualSpecCase.getInfFlowSpecs());
        return clauses;
    }

    private void translateAccessible(Context context, ProgramVariableCollection progVars,
            LocationVariable heap, LocationVariable heapAtPre, final LocationVariable savedHeap,
            ImmutableList<LabeledParserRuleContext> accessible,
            ImmutableList<LabeledParserRuleContext> accessiblePre, ContractClauses clauses)
            throws SLTranslationException {
        if (heap == savedHeap && accessible.isEmpty()) {
            clauses.accessibles.put(heap, null);
            clauses.accessibles.put(heapAtPre, null);
        } else {
            clauses.accessibles.put(heap, translateAssignable(context, progVars.paramVars,
                progVars.atPres, progVars.atBefores, accessible));
            clauses.accessibles.put(heapAtPre, translateAssignable(context, progVars.paramVars,
                progVars.atPres, progVars.atBefores, accessiblePre));
        }
    }

    private void translateAxioms(Context context, ProgramVariableCollection progVars,
            LocationVariable heap, ImmutableList<LabeledParserRuleContext> axioms,
            ContractClauses clauses, Behavior originalBehavior) {
        boolean empty = axioms.isEmpty() // either the list is empty
                || (axioms.size() == 1 // or the first element is an empty method_decl
                        && axioms.head().first instanceof JmlParser.Method_declarationContext
                        && ((JmlParser.Method_declarationContext) axioms.head().first)
                                .method_body() == null);
        if (empty) {
            clauses.axioms.put(heap, null);
        } else {
            clauses.axioms.put(heap,
                translateEnsures(context, progVars.paramVars, progVars.resultVar, progVars.excVar,
                    progVars.atPres, progVars.atBefores, originalBehavior, axioms));
        }
    }

    private void translateEnsures(Context context, ProgramVariableCollection progVars,
            LocationVariable heap, final LocationVariable savedHeap,
            ImmutableList<LabeledParserRuleContext> ensures,
            ImmutableList<LabeledParserRuleContext> ensuresFree, ContractClauses clauses,
            Behavior originalBehavior) {
        if (heap == savedHeap && ensures.isEmpty()) {
            clauses.ensures.put(heap, null);
        } else {
            clauses.ensures.put(heap,
                translateEnsures(context, progVars.paramVars, progVars.resultVar, progVars.excVar,
                    progVars.atPres, progVars.atBefores, originalBehavior, ensures));
        }

        if (heap == savedHeap && ensuresFree.isEmpty()) {
            clauses.ensuresFree.put(heap, null);
        } else {
            clauses.ensuresFree.put(heap,
                translateAndClauses(context, progVars.paramVars, progVars.resultVar,
                    progVars.excVar, progVars.atPres, progVars.atBefores, ensuresFree,
                    SpecType.ENSURES_FREE));
        }
    }

    private void translateRequires(Context context, ProgramVariableCollection progVars,
            LocationVariable heap, final LocationVariable savedHeap,
            final ImmutableList<LabeledParserRuleContext> requires,
            final ImmutableList<LabeledParserRuleContext> requiresFree, ContractClauses clauses) {
        if (heap == savedHeap && requires.isEmpty()) {
            clauses.requires.put(heap, null);
        } else {
            clauses.requires.put(heap, translateAndClauses(context, progVars.paramVars, null, null,
                progVars.atPres, progVars.atBefores, requires, SpecType.REQUIRES));
        }
        if (heap == savedHeap && requiresFree.isEmpty()) {
            clauses.requiresFree.put(heap, null);
        } else {
            clauses.requiresFree.put(heap, translateAndClauses(context, progVars.paramVars, null,
                null, progVars.atPres, progVars.atBefores, requiresFree, SpecType.REQUIRES_FREE));
        }
    }

    private void translateAssignable(Context context, ProgramVariableCollection progVars,
            LocationVariable heap, final LocationVariable savedHeap,
            final ImmutableList<LabeledParserRuleContext> assignable,
            final ImmutableList<LabeledParserRuleContext> assignableFree, ContractClauses clauses)
            throws SLTranslationException {
        clauses.hasAssignable.put(heap,
            !translateStrictlyPure(context, progVars.paramVars, assignable));

        // For the frame condition, the default if there is no _free term is strictly_nothing.
        clauses.hasFreeAssignable.put(heap,
            !assignableFree.isEmpty()
                    && !translateStrictlyPure(context, progVars.paramVars, assignableFree));

        if (heap == savedHeap && assignable.isEmpty()) {
            clauses.assignables.put(heap, null);
        } else {
            final Boolean hasAssignable = clauses.hasAssignable.get(heap);
            if (hasAssignable == null || !hasAssignable) {
                final ImmutableList<LabeledParserRuleContext> assignableNothing =
                    ImmutableSLList.<LabeledParserRuleContext>nil().append(getAssignableNothing());
                clauses.assignables.put(heap, translateAssignable(context, progVars.paramVars,
                    progVars.atPres, progVars.atBefores, assignableNothing));
            } else {
                clauses.assignables.put(heap, translateAssignable(context, progVars.paramVars,
                    progVars.atPres, progVars.atBefores, assignable));
            }
        }

        if (heap == savedHeap && assignableFree.isEmpty()) {
            clauses.assignablesFree.put(heap, null);
        } else {
            final Boolean hasFreeAssignable = clauses.hasFreeAssignable.get(heap);
            if (hasFreeAssignable == null || !hasFreeAssignable) {
                final ImmutableList<LabeledParserRuleContext> assignableFreeNothing =
                    ImmutableSLList
                            .<LabeledParserRuleContext>nil().append(getAssignableFreeNothing());
                clauses.assignablesFree.put(heap,
                    translateAssignableFree(context, progVars.paramVars,
                        progVars.atPres, progVars.atBefores, assignableFreeNothing));
            } else {
                clauses.assignablesFree.put(heap,
                    translateAssignableFree(context, progVars.paramVars,
                        progVars.atPres, progVars.atBefores, assignableFree));
            }
        }

    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    private @NonNull LabeledParserRuleContext getAssignableNothing() {
        return new LabeledParserRuleContext(JmlFacade.parseClause("assignable \\nothing;"),
            ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL);
    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    private @NonNull LabeledParserRuleContext getAssignableFreeNothing() {
        return new LabeledParserRuleContext(JmlFacade.parseClause("assignable_free \\nothing;"),
            ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL);
    }

    /**
     * register abbreviations in contracts (aka. old clauses). creates update terms.
     */
    private ImmutableList<Term> registerAbbreviationVariables(TextualJMLSpecCase textualSpecCase,
            Context context, ProgramVariableCollection progVars, ContractClauses clauses) {
        for (Triple<LabeledParserRuleContext, LabeledParserRuleContext, LabeledParserRuleContext> abbrv : textualSpecCase
                .getAbbreviations()) {
            final KeYJavaType abbrKJT =
                services.getJavaInfo().getKeYJavaType(abbrv.first.first.getText());
            final ProgramElementName abbrVarName =
                new ProgramElementName(abbrv.second.first.getText());
            final LocationVariable abbrVar = new LocationVariable(abbrVarName, abbrKJT, true, true);
            assert abbrVar.isGhost() : "specification parameter not ghost";
            services.getNamespaces().programVariables().addSafely(abbrVar);
            progVars.paramVars = progVars.paramVars.append(abbrVar); // treat as
            // (ghost)
            // parameter
            Term rhs = new JmlIO(services).context(context).parameters(progVars.paramVars)
                    .atPres(progVars.atPres).atBefore(progVars.atBefores)
                    .translateTerm(abbrv.third);
            clauses.abbreviations =
                clauses.abbreviations.append(tb.elementary(tb.var(abbrVar), rhs));
        }
        return clauses.abbreviations;
    }

    private ImmutableList<InfFlowSpec> translateInfFlowSpecClauses(Context context,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, ImmutableList<LabeledParserRuleContext> originalClauses) {
        if (originalClauses.isEmpty()) {
            return ImmutableSLList.nil();
        } else {
            ImmutableList<InfFlowSpec> result = ImmutableSLList.nil();
            for (LabeledParserRuleContext expr : originalClauses) {
                InfFlowSpec translated = new JmlIO(services).context(context).parameters(paramVars)
                        .resultVariable(resultVar).exceptionVariable(excVar).translateInfFlow(expr);
                if (translated != null) {
                    result = result.append(translated);
                }
            }
            return result;
        }
    }

    /**
     * Clauses are expected to be conjoined in a right-associative way, i.e. A & (B & ( C (...&
     * N))). When using auto induction with lemmas, then A will be used as a lemma for B, A & B will
     * be used as a lemma for C and so on. This mimics the Isabelle-style of proving.
     */
    private Term translateAndClauses(Context context, ImmutableList<LocationVariable> paramVars,
            LocationVariable resultVar, LocationVariable excVar, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, Term> atBefores,
            ImmutableList<LabeledParserRuleContext> originalClauses, SpecType specType) {
        // The array is used to invert the order in which the elements are read.
        LabeledParserRuleContext[] array = new LabeledParserRuleContext[originalClauses.size()];
        originalClauses.toArray(array);

        var io =
            new JmlIO(services).context(context).parameters(paramVars).resultVariable(resultVar)
                    .exceptionVariable(excVar).atPres(atPres).atBefore(atBefores);

        Term result = tb.tt();
        for (int i = array.length - 1; i >= 0; i--) {
            Term translated = io.translateTerm(array[i], specType);
            Term translatedFormula = tb.convertToFormula(translated);
            result = tb.andSC(translatedFormula, result);
        }
        return result;
    }

    private Term translateOrClauses(Context context, ImmutableList<LocationVariable> paramVars,
            ImmutableList<LabeledParserRuleContext> originalClauses) {
        Term result = tb.ff();
        for (LabeledParserRuleContext expr : originalClauses) {
            Term translated =
                new JmlIO(services).context(context).parameters(paramVars).translateTerm(expr);
            result = tb.orSC(result, tb.convertToFormula(translated));
        }
        return result;
    }

    private Term translateUnionClauses(Context context, ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores,
            ImmutableList<LabeledParserRuleContext> originalClauses, SpecType specType)
            throws SLTranslationException {
        Term result = tb.empty();
        for (LabeledParserRuleContext expr : originalClauses) {
            Term translated = new JmlIO(services).context(context).parameters(paramVars)
                    .atPres(atPres).atBefore(atBefores).translateTerm(expr, specType);

            // less than nothing is marked by some special term
            if (translated.equalsModProperty(tb.strictlyNothing(),
                IRRELEVANT_TERM_LABELS_PROPERTY)) {
                if (originalClauses.size() > 1) {
                    throw new SLTranslationException(
                        "\"assignable \\strictly_nothing\" cannot be joined with other "
                            + "\"assignable\" clauses (even if they declare the same).",
                        Location.fromToken(expr.first.start));
                }
                return tb.empty();
            }

            result = tb.union(result, translated);
        }

        return result;
    }

    private Map<Label, Term> translateBreaks(Context context,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
            ImmutableList<LabeledParserRuleContext> originalClauses) {
        LabeledParserRuleContext[] array = new LabeledParserRuleContext[originalClauses.size()];
        originalClauses.toArray(array);
        Map<Label, Term> result = new LinkedHashMap<>();
        for (int i = array.length - 1; i >= 0; i--) {
            Pair<Label, Term> translation =
                new JmlIO(services).context(context).parameters(paramVars).resultVariable(resultVar)
                        .exceptionVariable(excVar).atPres(atPres).atBefore(atBefores)
                        .translateLabeledClause(array[i], SpecType.BREAKS);
            result.put(translation.first, translation.second);
        }
        return result;
    }

    private Map<Label, Term> translateContinues(Context context,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
            ImmutableList<LabeledParserRuleContext> originalClauses) {
        LabeledParserRuleContext[] array = new LabeledParserRuleContext[originalClauses.size()];
        originalClauses.toArray(array);
        Map<Label, Term> result = new LinkedHashMap<>();
        for (int i = array.length - 1; i >= 0; i--) {
            Pair<Label, Term> translation =
                new JmlIO(services).context(context).parameters(paramVars).resultVariable(resultVar)
                        .exceptionVariable(excVar).atPres(atPres).atBefore(atBefores)
                        .translateLabeledClause(array[i], SpecType.CONTINUES);
            result.put(translation.first, translation.second);
        }
        return result;
    }

    private Term translateReturns(Context context, ImmutableList<LocationVariable> paramVars,
            LocationVariable resultVar, LocationVariable excVar, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
            ImmutableList<LabeledParserRuleContext> originalClauses) {
        if (originalBehavior == Behavior.NORMAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return tb.ff();
        } else {
            return translateAndClauses(context, paramVars, resultVar, excVar, atPres, atBefores,
                originalClauses, SpecType.RETURNS);
        }
    }

    private Term translateSignals(Context context, ImmutableList<LocationVariable> paramVars,
            LocationVariable resultVar, LocationVariable excVar, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
            ImmutableList<LabeledParserRuleContext> originalClauses) {
        if (originalBehavior == Behavior.NORMAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return tb.ff();
        } else {
            return translateAndClauses(context, paramVars, resultVar, excVar, atPres, atBefores,
                originalClauses, SpecType.SIGNALS);
        }
    }

    private Term translateSignalsOnly(Context context, LocationVariable excVar,
            Behavior originalBehavior, ImmutableList<LabeledParserRuleContext> originalClauses) {
        return translateSignals(context, null, null, excVar, null, null, originalBehavior,
            originalClauses);
    }

    private Term translateEnsures(Context context, ImmutableList<LocationVariable> paramVars,
            LocationVariable resultVar, LocationVariable excVar, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
            ImmutableList<LabeledParserRuleContext> originalClauses) {
        if (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR) {
            if (!originalClauses.isEmpty()) {
                throw new IllegalArgumentException(
                    "An exceptional_behavior contract is not allowed to have ensures clauses.");
            }
            return tb.ff();
        } else {
            return translateAndClauses(context, paramVars, resultVar, excVar, atPres, atBefores,
                originalClauses, SpecType.ENSURES);
        }
    }

    @SuppressWarnings("unused")
    private Term translateAccessible(Context context, ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores,
            ImmutableList<LabeledParserRuleContext> originalClauses) throws SLTranslationException {
        if (originalClauses.isEmpty()) {
            return tb.allLocs();
        } else {
            return translateUnionClauses(context, paramVars, atPres, atBefores, originalClauses,
                SpecType.ACCESSIBLE);
        }
    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    private Term translateAssignable(Context context, ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores,
            ImmutableList<LabeledParserRuleContext> originalClauses) throws SLTranslationException {

        if (originalClauses.isEmpty()) {
            return tb.allLocs();
        } else {
            return translateUnionClauses(context, paramVars, atPres, atBefores, originalClauses,
                SpecType.ASSIGNABLE);
        }
    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    private Term translateAssignableFree(Context context, ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores,
            ImmutableList<LabeledParserRuleContext> originalClauses) throws SLTranslationException {
        // If originalClauses.isEmpty, the default value for _free is strictly_nothing,
        // which cannot be represented by a LocSet term.
        assert !originalClauses.isEmpty();
        return translateUnionClauses(context, paramVars, atPres, atBefores, originalClauses,
            SpecType.ASSIGNABLE_FREE);
    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    private boolean translateStrictlyPure(Context context,
            ImmutableList<LocationVariable> paramVars,
            ImmutableList<LabeledParserRuleContext> assignableClauses) {

        for (LabeledParserRuleContext expr : assignableClauses) {
            Term translated =
                new JmlIO(services).context(context).parameters(paramVars).translateTerm(expr);

            // less than nothing is marked by some special term
            if (translated.equalsModProperty(tb.strictlyNothing(),
                IRRELEVANT_TERM_LABELS_PROPERTY)) {
                return true;
            }
        }

        return false;
    }

    private Term translateMeasuredBy(Context context, ImmutableList<LocationVariable> paramVars,
            ImmutableList<LabeledParserRuleContext> originalMeasuredBy) {
        Term measuredBy = null;
        if (!originalMeasuredBy.isEmpty()) {
            for (LabeledParserRuleContext expr : originalMeasuredBy) {
                Term translated =
                    new JmlIO(services).context(context).parameters(paramVars).translateTerm(expr);
                if (measuredBy == null) {
                    measuredBy = translated;
                } else {
                    measuredBy = tb.pair(measuredBy, translated);
                }
            }
        }
        return measuredBy;
    }

    private Term translateDecreases(Context context, ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores,
            ImmutableList<LabeledParserRuleContext> originalDecreases) {
        Term decreases = null;
        if (!originalDecreases.isEmpty()) {
            for (LabeledParserRuleContext expr : originalDecreases) {
                Term translated = new JmlIO(services).context(context).parameters(paramVars)
                        .atPres(atPres).atBefore(atBefores).translateTerm(expr, SpecType.DECREASES);
                if (decreases == null) {
                    decreases = translated;
                } else {
                    decreases = tb.pair(decreases, translated);
                }
            }
        }
        return decreases;
    }

    public String generateName(IProgramMethod pm, TextualJMLSpecCase textualSpecCase,
            Behavior originalBehavior) {
        String customName = textualSpecCase.getName();
        return generateName(pm, originalBehavior, customName);
    }

    public String generateName(IProgramMethod pm, Behavior originalBehavior, String customName) {
        return ((!(customName == null) && customName.length() > 0) ? customName
                : getContractName(pm, originalBehavior));
    }

    private Map<LocationVariable, Term> generatePostCondition(ProgramVariableCollection progVars,
            ContractClauses clauses, Behavior originalBehavior) {
        Map<LocationVariable, Term> result = new LinkedHashMap<>();
        if (progVars.excVar == null) { // Model methods do not have exceptions
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.ensures.get(heap) != null) {
                    Term post = tb.convertToFormula(clauses.ensures.get(heap));
                    result.put(heap, post);
                }
            }
        } else {
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.ensures.get(heap) != null) {
                    Term excNull = tb.addLabelToAllSubs(
                        (tb.label(tb.equals(tb.var(progVars.excVar), tb.NULL()),
                            ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)),
                        new Origin(SpecType.ENSURES));
                    Term post1 = (originalBehavior == Behavior.NORMAL_BEHAVIOR
                            ? tb.convertToFormula(clauses.ensures.get(heap))
                            : tb.imp(excNull, tb.convertToFormula(clauses.ensures.get(heap))));
                    Term post2 = (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR
                            ? tb.and(tb.convertToFormula(clauses.signals),
                                tb.convertToFormula(clauses.signalsOnly))
                            : tb.imp(tb.not(excNull), tb.and(tb.convertToFormula(clauses.signals),
                                tb.convertToFormula(clauses.signalsOnly))));

                    Term post = heap == services.getTypeConverter().getHeapLDT().getHeap()
                            ? tb.and(post1, post2)
                            : post1;

                    result.put(heap, post);
                } else {
                    if (clauses.assignables.get(heap) != null) {
                        result.put(heap, tb.tt());
                    }
                }
            }
        }
        return result;
    }

    private Map<LocationVariable, Term> generateRepresentsAxioms(ProgramVariableCollection progVars,
            ContractClauses clauses, Behavior originalBehavior) {
        Map<LocationVariable, Term> result = new LinkedHashMap<>();
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            if (clauses.axioms.get(heap) != null) {
                result.put(heap, tb.convertToFormula(clauses.axioms.get(heap)));
            }
        }
        return result;
    }

    /**
     * Generate functional operation contracts.
     *
     * @param name base name of the contract (does not have to be unique)
     * @param pm the IProgramMethod to which the contract belongs
     * @param progVars pre-generated collection of variables for the receiver object, operation
     *        parameters, operation result, thrown exception and the pre-heap
     * @param clauses pre-translated JML clauses
     * @return operation contracts including new functional operation contracts
     */
    public ImmutableSet<Contract> createFunctionalOperationContracts(String name, IProgramMethod pm,
            ProgramVariableCollection progVars, ContractClauses clauses,
            Map<LocationVariable, Term> posts, Map<LocationVariable, Term> axioms) {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();

        Term abbrvLhs = null;
        if (!clauses.abbreviations.isEmpty()) {
            abbrvLhs = tb.sequential(clauses.abbreviations);
        }

        // requires
        Map<LocationVariable, Term> pres = new LinkedHashMap<>();
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            if (clauses.requires.get(heap) != null) {
                Term pre = tb.convertToFormula(clauses.requires.get(heap));
                pres.put(heap, pre);
            } else {
                if (clauses.assignables.get(heap) != null) {
                    pres.put(heap, tb.tt());
                }
            }
        }

        // diverges
        if (clauses.diverges.equals(tb.ff())) {
            // create diamond modality contract
            FunctionalOperationContract contract = cf.func(name, pm, true, pres,
                clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                clauses.assignables, clauses.assignablesFree, clauses.accessibles,
                clauses.hasAssignable, clauses.hasFreeAssignable, progVars);
            contract = cf.addGlobalDefs(contract, abbrvLhs);
            result = result.add(contract);
        } else if (clauses.diverges.equals(tb.tt())) {
            // create box modality contract
            FunctionalOperationContract contract = cf.func(name, pm, false, pres,
                clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                clauses.assignables, clauses.assignablesFree, clauses.accessibles,
                clauses.hasAssignable, clauses.hasFreeAssignable, progVars);
            contract = cf.addGlobalDefs(contract, abbrvLhs);
            result = result.add(contract);
        } else {
            // create two contracts for each diamond and box modality
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.requires.get(heap) != null) {
                    pres.put(heap,
                        tb.andSC(pres.get(heap), tb.not(tb.convertToFormula(clauses.diverges))));
                    break;
                }
            }
            FunctionalOperationContract contract1 = cf.func(name, pm, true, pres,
                clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                clauses.assignables, clauses.assignablesFree, clauses.accessibles,
                clauses.hasAssignable, clauses.hasFreeAssignable, progVars);
            contract1 = cf.addGlobalDefs(contract1, abbrvLhs);
            FunctionalOperationContract contract2 = cf.func(name, pm, false, clauses.requires,
                clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                clauses.assignables, clauses.assignablesFree, clauses.accessibles,
                clauses.hasAssignable, clauses.hasFreeAssignable, progVars);
            contract2 = cf.addGlobalDefs(contract2, abbrvLhs);
            result = result.add(contract1).add(contract2);
        }
        return result;
    }

    /**
     * Generate dependency operation contract out of the JML accessible clause.
     *
     * @param pm the IProgramMethod to which the contract belongs
     * @param progVars collection of variables for the receiver object, operation parameters,
     *        operation result, thrown exception and the pre-heap
     * @param clauses pre-translated JML clauses
     * @return operation contracts including a new dependency contract
     */
    private ImmutableSet<Contract> createDependencyOperationContract(IProgramMethod pm,
            ProgramVariableCollection progVars, ContractClauses clauses) {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();

        Term abbrvLhs = null;
        if (!clauses.abbreviations.isEmpty()) {
            abbrvLhs = tb.sequential(clauses.abbreviations);
        }

        boolean createContract = true;
        for (LocationVariable heap : HeapContext.getModifiableHeaps(services, false)) {
            if (clauses.accessibles.get(heap).equalsModProperty(tb.allLocs(),
                RENAMING_PROPERTY)) {
                createContract = false;
                break;
            }
            if (pm.isModel() && pm.getStateCount() > 1) {
                if (clauses.accessibles.get(progVars.atPreVars.get(heap))
                        .equalsModProperty(tb.allLocs(), RENAMING_PROPERTY)) {
                    createContract = false;
                    break;
                }
            } else if (pm.isModel() && pm.getStateCount() == 0) {
                createContract = false;
                break;
            }
        }
        if (createContract) {
            assert (progVars.selfVar == null) == pm.isStatic();
            Map<LocationVariable, Term> pres = new LinkedHashMap<>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.requires.get(heap) != null) {
                    final Term pre = tb.convertToFormula(clauses.requires.get(heap));
                    pres.put(heap, pre);
                }
            }
            final Contract depContract = cf.dep(pm.getContainerType(), pm, pm.getContainerType(),
                pres, clauses.measuredBy, clauses.accessibles, progVars.selfVar, progVars.paramVars,
                progVars.atPreVars, abbrvLhs);
            result = result.add(depContract);
        }
        return result;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------
    public ClassInvariant createJMLClassInvariant(@NonNull KeYJavaType kjt,
            VisibilityModifier visibility, boolean isStatic,
            @NonNull LabeledParserRuleContext originalInv) {
        var context = Context.inClass(kjt, isStatic, tb);

        // translateToTerm expression
        final Term inv0 = new JmlIO(services).context(context).translateTerm(originalInv);
        Term inv = tb.convertToFormula(inv0);
        // create invariant
        String name = getDefaultInvName(null, kjt);
        return new ClassInvariantImpl(name, name, kjt, visibility, inv, context.selfVar());
    }

    public ClassInvariant createJMLClassInvariant(KeYJavaType kjt, TextualJMLClassInv textualInv) {
        // check whether the invariant is static
        final ImmutableList<JMLModifier> modifiers = textualInv.getModifiers();
        final boolean isStatic = (modifiers.contains(JMLModifier.STATIC) || // modifier
        // "static"
        // in an interface "static" is the default (see Sect. 2.5 of the
        // reference manual)
                (services.getJavaInfo().isInterface(kjt)
                        && !modifiers.contains(JMLModifier.INSTANCE)));

        // create variable for self
        var context = Context.inClass(kjt, isStatic, tb);

        // translateToTerm expression
        final Term inv0 = new JmlIO(services).context(context).translateTerm(textualInv.getInv());
        Term inv = tb.convertToFormula(inv0);
        // create invariant
        String name = getDefaultInvName(null, kjt);
        String display = getDefaultInvName(textualInv.getName(), kjt);
        return new ClassInvariantImpl(name, display, kjt, getVisibility(textualInv), inv,
            context.selfVar(), textualInv.isFree());
    }

    public InitiallyClause createJMLInitiallyClause(@NonNull KeYJavaType kjt,
            VisibilityModifier visibility, @NonNull LabeledParserRuleContext original) {
        var context = Context.inClass(kjt, false, tb);

        // translateToTerm expression
        final Term inv0 = new JmlIO(services).context(context).translateTerm(original);

        Term inv = tb.convertToFormula(inv0);

        // create invariant
        String name = getInicName();
        return new InitiallyClauseImpl(name, name, kjt, new Public(), inv, context.selfVar(),
            original);

    }

    public InitiallyClause createJMLInitiallyClause(KeYJavaType kjt,
            TextualJMLInitially textualInv) {
        return createJMLInitiallyClause(kjt, getVisibility(textualInv), textualInv.getInv());
    }

    public ClassAxiom createJMLRepresents(@NonNull KeYJavaType kjt, VisibilityModifier visibility,
            @NonNull LabeledParserRuleContext originalRep, boolean isStatic)
            throws SLTranslationException {

        var context = Context.inClass(kjt, isStatic, tb);

        // translateToTerm expression
        final Pair<IObserverFunction, Term> rep =
            new JmlIO(services).context(context).translateRepresents(originalRep);
        // represents clauses must be unique per type
        for (Pair<KeYJavaType, IObserverFunction> p : modelFields) {
            if (p.first.equals(kjt) && p.second.equals(rep.first)) {
                throw new SLTranslationException(
                    "JML represents clauses must occur uniquely per type and target.",
                    Location.fromToken(originalRep.first.start));
            }
        }
        modelFields.add(new Pair<>(kjt, rep.first));
        Term repFormula = tb.convertToFormula(rep.second);
        // create class axiom
        return new RepresentsAxiom("JML represents clause for " + rep.first.name(), rep.first, kjt,
            visibility, null, repFormula, context.selfVar(), ImmutableSLList.nil(), null);
    }

    public ClassAxiom createJMLRepresents(KeYJavaType kjt, TextualJMLRepresents textualRep)
            throws SLTranslationException {

        boolean isStatic = textualRep.getModifiers().contains(JMLModifier.STATIC);
        var context = Context.inClass(kjt, isStatic, tb);

        // translateToTerm expression
        final LabeledParserRuleContext clause = textualRep.getRepresents();
        final Pair<IObserverFunction, Term> rep =
            new JmlIO(services).context(context).translateRepresents(clause);

        // check whether there already is a represents clause
        if (!modelFields.add(new Pair<>(kjt, rep.first))) {
            Token start = clause.first.start;
            throw new SLWarningException(
                "JML represents clauses must occur uniquely per " + "type and target."
                    + "\nAll but one are ignored.",
                Location.fromToken(start));
        }
        // create class axiom
        String name = "JML represents clause for " + rep.first.name();
        String displayName = textualRep.getName() == null ? name
                : "JML represents clause \"" + textualRep.getName() + "\" for " + rep.first.name();
        Term repFormula = tb.convertToFormula(rep.second);
        return new RepresentsAxiom(name, displayName, rep.first, kjt, getVisibility(textualRep),
            null, repFormula, context.selfVar(), ImmutableSLList.nil(), null);
    }

    /**
     * Creates a class axiom from a textual JML representation. As JML axioms are always without
     * modifiers, they are implicitly non-static and public.
     *
     * @param kjt the type where the axiom is declared
     * @param textual textual representation
     * @return created {@link ClassAxiom}
     */
    public ClassAxiom createJMLClassAxiom(@NonNull KeYJavaType kjt, TextualJMLClassAxiom textual) {
        LabeledParserRuleContext originalRep = textual.getAxiom();
        if (originalRep == null) {
            throw new NullPointerException();
        }

        var context = Context.inClass(kjt, false, tb);

        // translate expression
        final Term inv0 = new JmlIO(services).context(context).translateTerm(originalRep);
        final Term ax = tb.convertToFormula(inv0);

        // create class axiom
        String name = "class axiom in " + kjt.getFullName();
        String displayName = textual.getName() == null ? name
                : "class axiom \"" + textual.getName() + "\" in " + kjt.getFullName();
        return new ClassAxiomImpl(name, displayName, kjt, new Public(), ax, context.selfVar());
    }

    public Contract createJMLDependencyContract(KeYJavaType kjt, LocationVariable targetHeap,
            LabeledParserRuleContext originalDep) {
        if (kjt == null) {
            throw new NullPointerException();
        }
        if (originalDep == null) {
            throw new NullPointerException();
        }

        var context = Context.inClass(kjt, false, tb);

        // translateToTerm expression
        Triple<IObserverFunction, Term, Term> dep =
            new JmlIO(services).context(context).translateDependencyContract(originalDep);
        return cf.dep(kjt, targetHeap, dep, dep.first.isStatic() ? null : context.selfVar());
    }

    public Contract createJMLDependencyContract(KeYJavaType kjt, TextualJMLDepends textualDep) {
        LabeledParserRuleContext dep = null;
        LocationVariable targetHeap = null;
        for (LocationVariable heap : HeapContext.getModifiableHeaps(services, false)) {
            ImmutableList<LabeledParserRuleContext> depends = textualDep.getDepends(heap.name());
            if (!depends.isEmpty()) {
                dep = textualDep.getDepends(heap.name()).head();
                targetHeap = heap;
                break;
            }
        }
        return createJMLDependencyContract(kjt, targetHeap, dep);
    }

    /**
     * Creates operation contracts out of the passed JML specification.
     *
     * @param pm corresponding program method
     * @param textualSpecCase textual representation of spec
     * @return created JML operation contracts
     * @throws SLTranslationException a translation exception
     */
    public ImmutableSet<Contract> createJMLOperationContracts(IProgramMethod pm,
            TextualJMLSpecCase textualSpecCase) throws SLTranslationException {
        if (pm == null) {
            throw new NullPointerException();
        }
        if (textualSpecCase == null) {
            throw new NullPointerException();
        }

        Behavior originalBehavior =
            pm.isModel() ? Behavior.MODEL_BEHAVIOR : textualSpecCase.getBehavior();

        String name = generateName(pm, textualSpecCase, originalBehavior);

        // prepare program variables, translateToTerm JML clauses and generate
        // post
        // condition

        ProgramVariableCollection progVars = createProgramVariables(pm);
        var context = Context.inMethodWithSelfVar(pm, progVars.selfVar);
        ContractClauses clauses =
            translateJMLClauses(textualSpecCase, context, progVars, originalBehavior);
        Map<LocationVariable, Term> posts =
            generatePostCondition(progVars, clauses, originalBehavior);
        Map<LocationVariable, Term> axioms =
            generateRepresentsAxioms(progVars, clauses, originalBehavior);

        // create contracts
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();
        result = result.union(createInformationFlowContracts(clauses, pm, progVars));
        result = result.union(
            createFunctionalOperationContracts(name, pm, progVars, clauses, posts, axioms));
        result = result.union(createDependencyOperationContract(pm, progVars, clauses));

        return result;
    }

    public ImmutableSet<MergeContract> createJMLMergeContracts(final IProgramMethod method,
            final MergePointStatement mps, final TextualJMLMergePointDecl mergePointDecl)
            throws SLTranslationException {

        final JmlParser.Merge_point_statementContext ctx = mergePointDecl.getMergeProc();

        // default merge procedure is MergeByIfThenElse
        final String mergeProcStr = ctx.proc == null ? MergeByIfThenElse.instance().toString()
                : ctx.proc.getText().replaceAll("\"", "");

        MergeProcedure mergeProc = MergeProcedure.getProcedureByName(mergeProcStr);
        if (mergeProc == null) {
            throw new SLTranslationException(
                format("Unknown merge procedure: \"%s\"", mergeProcStr),
                mergePointDecl.getLocation());
        }
        ImmutableSet<MergeContract> result = DefaultImmutableSet.nil();

        KeYJavaType kjt = method.getContainerType();
        if (mergeProc instanceof UnparametricMergeProcedure) {
            final UnparameterizedMergeContract unparameterizedMergeContract =
                new UnparameterizedMergeContract(mergeProc, mps, kjt);
            result = result.add(unparameterizedMergeContract);
        } else if (mergeProc instanceof ParametricMergeProcedure) { // arguments expected looking
                                                                    // for params
            if (!(mergeProc instanceof MergeWithPredicateAbstraction)) {
                throw new IllegalStateException("Currently, MergeWithPredicateAbstraction(Factory) "
                    + "is the only supported ParametricMergeProcedure");
            }

            // @formatter:off
            // Expected merge params structure:
            // merge_params <LATTICE-TYPE>: (<TYPE> <PLACHOLDER>) -> {<JML-FORMULA>}
            // @formatter:on
            final ProgramVariableCollection progVars = createProgramVariables(method);
            var context = Context.inMethodWithSelfVar(method, progVars.selfVar);

            // Determine the variables in "\old(...)" expressions and register
            // remembrance variables for them
            final ImmutableList<LocationVariable> params = method.collectParameters();
            final Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
            final ImmutableList<LocationVariable> allHeaps =
                services.getTypeConverter().getHeapLDT().getAllHeaps();
            allHeaps.forEach(
                heap -> atPres.put(heap, tb.var(tb.atPreVar(heap.toString(), heap.sort(), false))));
            params.forEach(param -> atPres.put(param,
                tb.var(tb.atPreVar(param.toString(), param.sort(), false))));

            final MergeParamsSpec specs = new JmlIO(services).context(context)
                    .parameters(append(ImmutableSLList.nil(), params))
                    .resultVariable(progVars.resultVar).exceptionVariable(progVars.excVar)
                    .atPres(atPres).translateMergeParams(ctx.mergeparamsspec());

            final Stream<Term> stream = specs.predicates().stream();
            final List<AbstractionPredicate> abstractionPredicates =
                stream.map(t -> AbstractionPredicate.create(t, specs.placeholder(), services))
                        .collect(Collectors.toList());

            result = result.add(new PredicateAbstractionMergeContract(mps, atPres, kjt,
                specs.latticeType(), abstractionPredicates));
        } else {
            throw new IllegalStateException(
                "MergeProcedures should either be an UnparametricMergeProcedure or a ParametricMergeProcedure");
        }
        return result;
    }

    /**
     * Creates a set of block contracts for a block from a textual specification case.
     *
     * @param method the method containing the block.
     * @param labels all labels belonging to the block.
     * @param block the block which the block contracts belong to.
     * @param specificationCase the textual specification case.
     * @return a set of block contracts for a block from a textual specification case.
     * @throws SLTranslationException translation exception
     */
    public ImmutableSet<BlockContract> createJMLBlockContracts(IProgramMethod method,
            List<Label> labels, StatementBlock block, TextualJMLSpecCase specificationCase)
            throws SLTranslationException {
        if (specificationCase.isLoopContract()) {
            return DefaultImmutableSet.nil();
        }

        final Behavior behavior = specificationCase.getBehavior();
        final AuxiliaryContract.Variables variables =
            AuxiliaryContract.Variables.create(block, labels, method, services);
        final ProgramVariableCollection programVariables =
            createProgramVariables(method, block, variables);
        var context = Context.inMethodWithSelfVar(method, programVariables.selfVar);
        final ContractClauses clauses =
            translateJMLClauses(specificationCase, context, programVariables, behavior);
        return new BlockContractImpl.Creator("JML " + behavior + "block contract", block, labels,
            method, behavior, variables, clauses.requires, clauses.requiresFree, clauses.measuredBy,
            clauses.ensures, clauses.ensuresFree, clauses.infFlowSpecs, clauses.breaks,
            clauses.continues, clauses.returns, clauses.signals, clauses.signalsOnly,
            clauses.diverges, clauses.assignables, clauses.assignablesFree,
            clauses.hasAssignable, clauses.hasFreeAssignable, services).create();
    }

    /**
     * Creates a set of loop contracts for a loop from a textual specification case.
     *
     * @param method the method containing the block.
     * @param labels all labels belonging to the block.
     * @param loop the loop which the loop contracts belong to.
     * @param specificationCase the textual specification case.
     * @return a set of loop contracts for a block from a textual specification case.
     * @throws SLTranslationException a translation exception
     */
    public ImmutableSet<LoopContract> createJMLLoopContracts(final IProgramMethod method,
            final List<Label> labels, final LoopStatement loop,
            final TextualJMLSpecCase specificationCase) throws SLTranslationException {
        if (!specificationCase.isLoopContract()) {
            return DefaultImmutableSet.nil();
        }

        final Behavior behavior = specificationCase.getBehavior();
        final AuxiliaryContract.Variables variables =
            AuxiliaryContract.Variables.create(loop, labels, method, services);
        final ProgramVariableCollection programVariables =
            createProgramVariables(method, loop, variables);
        var context = Context.inMethod(method, tb);
        final ContractClauses clauses =
            translateJMLClauses(specificationCase, context, programVariables, behavior);
        return new LoopContractImpl.Creator("JML " + behavior + "loop contract", loop, labels,
            method, behavior, variables, clauses.requires, clauses.requiresFree, clauses.measuredBy,
            clauses.ensures, clauses.ensuresFree, clauses.infFlowSpecs, clauses.breaks,
            clauses.continues, clauses.returns, clauses.signals, clauses.signalsOnly,
            clauses.diverges, clauses.assignables, clauses.assignablesFree, clauses.hasAssignable,
            clauses.hasFreeAssignable, clauses.decreases, services)
                    .create();
    }

    /**
     * Creates a set of loop contracts for a block from a textual specification case.
     *
     * @param method the method containing the block.
     * @param labels all labels belonging to the block.
     * @param block the block which the loop contracts belong to.
     * @param specificationCase the textual specification case.
     * @return a set of loop contracts for a block from a textual specification case.
     * @throws SLTranslationException a translation exception
     */
    public ImmutableSet<LoopContract> createJMLLoopContracts(IProgramMethod method,
            List<Label> labels, StatementBlock block, TextualJMLSpecCase specificationCase)
            throws SLTranslationException {

        if (!specificationCase.isLoopContract()) {
            return DefaultImmutableSet.nil();
        }

        final Behavior behavior = specificationCase.getBehavior();
        final AuxiliaryContract.Variables variables =
            AuxiliaryContract.Variables.create(block, labels, method, services);
        final ProgramVariableCollection programVariables =
            createProgramVariables(method, block, variables);
        var context = Context.inMethod(method, tb);
        final ContractClauses clauses =
            translateJMLClauses(specificationCase, context, programVariables, behavior);
        return new LoopContractImpl.Creator("JML " + behavior + "loop contract", block, labels,
            method, behavior, variables, clauses.requires, clauses.requiresFree, clauses.measuredBy,
            clauses.ensures, clauses.ensuresFree, clauses.infFlowSpecs, clauses.breaks,
            clauses.continues, clauses.returns, clauses.signals, clauses.signalsOnly,
            clauses.diverges, clauses.assignables, clauses.assignablesFree, clauses.hasAssignable,
            clauses.hasFreeAssignable, clauses.decreases, services)
                    .create();
    }

    private ProgramVariableCollection createProgramVariablesForStatement(Statement statement,
            IProgramMethod pm) {
        final Map<LocationVariable, LocationVariable> atPreVars = new LinkedHashMap<>();
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            atPreVars.put(heap, tb.atPreVar(heap.toString(), heap.sort(), true));
        }
        final ImmutableList<LocationVariable> parameters = pm.collectParameters();
        for (LocationVariable parameter : parameters) {
            atPreVars.put(parameter,
                tb.atPreVar(parameter.toString(), parameter.getKeYJavaType(), true));
        }
        final ImmutableList<LocationVariable> paramVars =
            append(collectLocalVariablesVisibleTo(statement, pm), parameters);
        return new ProgramVariableCollection(tb.selfVar(pm, pm.getContainerType(), false),
            paramVars, tb.resultVar(pm, false), tb.excVar(pm, false), atPreVars, termify(atPreVars),
            Collections.emptyMap(), // should be the pre-state of the enclosing contract
            Collections.emptyMap() // ignore for now
        );
    }

    /**
     * Translates the condition Term of a JmlAssert statement.
     *
     * @param jmlAssert the statement to create the condition for
     * @param pm the enclosing method
     */
    public void translateJmlAssertCondition(final JmlAssert jmlAssert, final IProgramMethod pm) {
        final var pv = createProgramVariablesForStatement(jmlAssert, pm);
        var io = new JmlIO(services).context(Context.inMethod(pm, tb))
                .selfVar(pv.selfVar)
                .parameters(pv.paramVars)
                .resultVariable(pv.resultVar)
                .exceptionVariable(pv.excVar)
                .atPres(pv.atPres)
                .atBefore(pv.atBefores);
        Term expr = io.translateTerm(jmlAssert.getCondition());
        services.getSpecificationRepository().addStatementSpec(
            jmlAssert,
            new SpecificationRepository.JmlStatementSpec(pv, ImmutableList.of(expr)));
    }

    public @Nullable String checkSetStatementAssignee(Term assignee) {
        if (assignee.op() instanceof LocationVariable) {
            var variable = (LocationVariable) assignee.op();
            if (variable.isGhost()) {
                return null;
            } else {
                return variable + " is not a ghost variable";
            }
        } else if (services.getTypeConverter().getHeapLDT().isSelectOp(assignee.op())) {
            Term field = assignee.subs().last();
            Operator op = field.op();
            SplitFieldName split = HeapLDT.trySplitFieldName(op);
            if (split != null) {
                ProgramVariable attribute =
                    services.getJavaInfo().getAttribute(split.attributeName(), split.className());
                if (attribute.isGhost()) {
                    return null;
                } else {
                    return op + " is not a ghost field";
                }
            } else if (op.equals(services.getTypeConverter().getHeapLDT().getArr())) {
                return "Arrays are not writeable using set statements";
            } else {
                return op + " is not a class field";
            }
        } else {
            return "Neither a field access nor a local variable access";
        }
    }

    /**
     * Translates a set statement.
     *
     * @param statement the set statement
     * @param pm the enclosing method
     */
    public void translateSetStatement(final SetStatement statement, final IProgramMethod pm)
            throws SLTranslationException {
        final var pv = createProgramVariablesForStatement(statement, pm);
        KeyAst.SetStatementContext setStatementContext = statement.getParserContext();
        var io = new JmlIO(services).context(Context.inMethod(pm, tb)).selfVar(pv.selfVar)
                .parameters(pv.paramVars)
                .resultVariable(pv.resultVar).exceptionVariable(pv.excVar).atPres(pv.atPres)
                .atBefore(pv.atBefores);
        Term assignee = io.translateTerm(setStatementContext.getAssignee());
        Term value = io.translateTerm(setStatementContext.getValue());
        if (value.sort() == JavaDLTheory.FORMULA) {
            value = tb.convertToBoolean(value);
        }
        String error = checkSetStatementAssignee(assignee);
        if (error != null) {
            throw new SLTranslationException(
                "Invalid assignment target for set statement: " + error,
                setStatementContext.getStartLocation());
        }

        services.getSpecificationRepository().addStatementSpec(
            statement,
            new SpecificationRepository.JmlStatementSpec(pv, ImmutableList.of(assignee, value)));
    }

    /**
     * Creates a program variable collection for a specified block. This collection contains all
     * program variables that occur freely in the block as parameters (i.e., in
     * {@link ProgramVariableCollection#paramVars}).
     *
     * @param method the method containing the block.
     * @param block the block.
     * @param variables an instance of {@link AuxiliaryContract.Variables} for the block.
     */
    private ProgramVariableCollection createProgramVariables(final IProgramMethod method,
            final JavaStatement block, final AuxiliaryContract.Variables variables) {
        final Map<LocationVariable, LocationVariable> remembranceVariables =
            variables.combineRemembranceVariables();
        final Map<LocationVariable, LocationVariable> outerRemembranceVariables =
            variables.combineOuterRemembranceVariables();

        ImmutableList<LocationVariable> vars;

        SourceElement first = block.getFirstElement();
        while (first instanceof LabeledStatement) {
            first = ((LabeledStatement) first).getBody();
        }

        if (first instanceof For) {
            vars = append(collectLocalVariables(method.getBody(), (For) first),
                method.collectParameters()).append(collectLocalVariablesVisibleTo(block, method));
        } else {
            vars = append(ImmutableSLList.nil(), method.collectParameters())
                    .append(collectLocalVariablesVisibleTo(block, method));
        }

        return new ProgramVariableCollection(variables.self, vars, variables.result,
            variables.exception, outerRemembranceVariables, termify(outerRemembranceVariables),
            remembranceVariables, termify(remembranceVariables));
    }

    private Map<LocationVariable, Term> termify(
            final Map<LocationVariable, LocationVariable> remembranceVariables) {
        final Map<LocationVariable, Term> result = new LinkedHashMap<>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : remembranceVariables
                .entrySet()) {
            result.put(remembranceVariable.getKey(), tb.var(remembranceVariable.getValue()));
        }
        return result;
    }

    protected ImmutableList<LocationVariable> collectLocalVariablesVisibleTo(
            final Statement statement, final IProgramMethod method) {
        return collectLocalVariablesVisibleTo(statement, method.getBody());
    }

    private ImmutableList<LocationVariable> collectLocalVariablesVisibleTo(Statement statement,
            StatementContainer container) {
        ImmutableList<LocationVariable> result = ImmutableSLList.nil();
        final int statementCount = container.getStatementCount();
        for (int i = 0; i < statementCount; i++) {
            final Statement s = container.getStatementAt(i);
            if (s instanceof For) {
                final ImmutableArray<VariableSpecification> variables =
                    ((For) s).getVariablesInScope();
                for (int j = 0; j < variables.size(); j++) {
                    result =
                        result.prepend((LocationVariable) variables.get(j).getProgramVariable());
                }
            }
            if (s == statement) {
                return result;
            } else if (s instanceof LocalVariableDeclaration) {
                final ImmutableArray<VariableSpecification> variables =
                    ((LocalVariableDeclaration) s).getVariables();
                for (int j = 0; j < variables.size(); j++) {
                    result =
                        result.prepend((LocationVariable) variables.get(j).getProgramVariable());
                }
            } else if (s instanceof StatementContainer) {
                final ImmutableList<LocationVariable> visibleLocalVariables =
                    collectLocalVariablesVisibleTo(statement, (StatementContainer) s);
                if (visibleLocalVariables != null) {
                    result = result.prepend(visibleLocalVariables);
                    return result;
                }
            } else if (s instanceof BranchStatement branch) {
                final int branchCount = branch.getBranchCount();
                for (int j = 0; j < branchCount; j++) {
                    final ImmutableList<LocationVariable> visibleLocalVariables =
                        collectLocalVariablesVisibleTo(statement, branch.getBranchAt(j));
                    if (visibleLocalVariables != null) {
                        result = result.prepend(visibleLocalVariables);
                        return result;
                    }
                }
            }
        }
        return null;
    }

    private LoopSpecification createJMLLoopInvariant(IProgramMethod pm, LoopStatement loop,
            Map<String, ImmutableList<LabeledParserRuleContext>> originalInvariants,
            Map<String, ImmutableList<LabeledParserRuleContext>> originalFreeInvariants,
            Map<String, ImmutableList<LabeledParserRuleContext>> originalModifiables,
            Map<String, ImmutableList<LabeledParserRuleContext>> originalFreeModifiables,
            ImmutableList<LabeledParserRuleContext> originalInfFlowSpecs,
            LabeledParserRuleContext originalVariant) {
        assert pm != null;
        assert loop != null;
        assert originalInvariants != null;
        assert originalModifiables != null;
        assert originalInfFlowSpecs != null;

        // create variables for self, parameters, other relevant local variables
        // (disguised as parameters to the translator) and the map for
        // atPre-Functions
        var context = Context.inMethod(pm, tb);
        final ImmutableList<LocationVariable> paramVars = pm.collectParameters();
        LocationVariable resultVar = tb.resultVar(pm, false);
        LocationVariable excVar = tb.excVar(pm, false); // only for information
        // flow

        final ImmutableList<LocationVariable> allHeaps =
            services.getTypeConverter().getHeapLDT().getAllHeaps();

        final Map<LocationVariable, Term> atPres = createAtPres(paramVars, allHeaps, tb);

        ImmutableList<LocationVariable> localVars = collectLocalVariables(pm.getBody(), loop);
        ImmutableList<LocationVariable> allVars = append(localVars, paramVars);

        // translateToTerm invariant
        final Map<LocationVariable, Term> invariants = translateToTermInvariants(context,
            originalInvariants, allVars, allHeaps, atPres, services, tb);

        Map<LocationVariable, Term> freeInvariants = translateToTermFreeInvariants(context,
            originalFreeInvariants, allVars, allHeaps, atPres, services, tb);

        // translateToTerm modifiable
        Map<LocationVariable, Term> modifiables =
            translateToTermModifiable(context, atPres, allVars, originalModifiables, false);
        Map<LocationVariable, Term> freeModifiables =
            translateToTermModifiable(context, atPres, allVars, originalFreeModifiables, true);


        // translateToTerm infFlowSpecs
        Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs =
            translateToTermInfFlowSpecs(context, resultVar, excVar, allVars, allHeaps,
                originalInfFlowSpecs);

        // translateToTerm variant
        Term variant = translateToTermVariant(context, atPres, allVars, originalVariant);

        ImmutableList<Term> localIns = tb.var(MiscTools.getLocalIns(loop, services));
        ImmutableList<Term> localOuts = tb.var(MiscTools.getLocalOuts(loop, services));

        // create loop invariant annotation
        Term selfTerm = context.selfVar() == null ? null : tb.var(context.selfVar());

        return new LoopSpecImpl(loop, pm, pm.getContainerType(), invariants, freeInvariants,
            modifiables, freeModifiables, infFlowSpecs, variant, selfTerm, localIns,
            localOuts, atPres);
    }

    private Term translateToTermVariant(Context context, Map<LocationVariable, Term> atPres,
            ImmutableList<LocationVariable> allVars, LabeledParserRuleContext originalVariant) {
        final Term variant;
        if (originalVariant == null) {
            variant = null;
        } else {
            variant = new JmlIO(services).context(context).parameters(allVars).atPres(atPres)
                    .atBefore(atPres).translateTerm(originalVariant, SpecType.DECREASES);
        }
        return variant;
    }

    private Map<LocationVariable, ImmutableList<InfFlowSpec>> translateToTermInfFlowSpecs(
            Context context, LocationVariable resultVar, LocationVariable excVar,
            ImmutableList<LocationVariable> allVars, final ImmutableList<LocationVariable> allHeaps,
            ImmutableList<LabeledParserRuleContext> originalInfFlowSpecs) {
        Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs = new LinkedHashMap<>();
        ImmutableList<InfFlowSpec> infFlowSpecTermList;
        final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        for (LocationVariable heap : allHeaps) {
            if (!originalInfFlowSpecs.isEmpty() && heap.equals(baseHeap)) {
                infFlowSpecTermList = translateInfFlowSpecClauses(context, allVars, resultVar,
                    excVar, originalInfFlowSpecs);
            } else {
                infFlowSpecTermList = ImmutableSLList.nil();
            }
            infFlowSpecs.put(heap, infFlowSpecTermList);
        }
        return infFlowSpecs;
    }

    private Map<LocationVariable, Term> translateToTermModifiable(Context context,
            Map<LocationVariable, Term> atPres, ImmutableList<LocationVariable> allVars,
            Map<String, ImmutableList<LabeledParserRuleContext>> originalModifiables,
            boolean free) {
        Map<LocationVariable, Term> modifiables = new LinkedHashMap<>();
        for (String h : originalModifiables.keySet()) {
            LocationVariable heap =
                services.getTypeConverter().getHeapLDT().getHeapForName(new Name(h));
            if (heap == null) {
                continue;
            }
            Term a;
            ImmutableList<LabeledParserRuleContext> as = originalModifiables.get(h);
            if (as.isEmpty()) {
                if (free) {
                    a = tb.strictlyNothing();
                } else {
                    a = tb.allLocs();
                }
            } else {
                a = tb.empty();
                for (LabeledParserRuleContext expr : as) {
                    Term translated =
                        new JmlIO(services).context(context).parameters(allVars).atPres(atPres)
                                .atBefore(atPres).translateTerm(expr,
                                    free ? SpecType.ASSIGNABLE_FREE : SpecType.ASSIGNABLE);
                    a = tb.union(a, translated);
                }
            }
            modifiables.put(heap, a);
        }
        return modifiables;
    }

    // ImmutableList does not accept lists of subclasses to #append and cannot
    // be lifted without changing the interface.
    // Hence this little helper.
    private ImmutableList<LocationVariable> append(ImmutableList<LocationVariable> localVars,
            ImmutableList<LocationVariable> paramVars) {
        ImmutableList<LocationVariable> result = ImmutableSLList.nil();
        for (LocationVariable param : paramVars) {
            result = result.prepend(param);
        }
        return result.prepend(localVars);
    }

    public LoopSpecification createJMLLoopInvariant(IProgramMethod pm, LoopStatement loop,
            TextualJMLLoopSpec textualLoopSpec) {
        return createJMLLoopInvariant(pm, loop, textualLoopSpec.getInvariants(),
            textualLoopSpec.getFreeInvariants(), textualLoopSpec.getAssignablesInit(),
            textualLoopSpec.getAssignablesFreeInit(), textualLoopSpec.getInfFlowSpecs(),
            textualLoopSpec.getVariant());
    }

    /**
     * Translate initially clause to a contract for the given constructor. Exception is thrown if
     * the methods passed is not a constructor. For an initially clause <tt>ini</tt> the resulting
     * contract looks like:<br>
     * <tt>requires true;<br>ensures ini;<br>signals (Exception) ini;<br>diverges true;</tt>
     *
     * @param ini initially clause
     * @param pm constructor
     * @return the translated (functional operation) contract
     * @throws SLTranslationException a translation exception
     */
    public FunctionalOperationContract initiallyClauseToContract(InitiallyClause ini,
            IProgramMethod pm) throws SLTranslationException {
        final ImmutableList<JMLModifier> modifiers =
            ImmutableSLList.<JMLModifier>nil().append(JMLModifier.PRIVATE);
        final TextualJMLSpecCase specCase = new TextualJMLSpecCase(modifiers, Behavior.NONE);
        specCase.addName(ini.getName());
        for (LabeledParserRuleContext context : createPrecond(pm, ini.getOriginalSpec())) {
            specCase.addClause(REQUIRES, context);
        }

        final String invariantFor = "\\invariant_for(this)";
        final LabeledParserRuleContext ctxFor = new LabeledParserRuleContext(
            JmlFacade.parseExpr(invariantFor), ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL);

        specCase.addClause(ENSURES, ctxFor);
        specCase.addClause(ENSURES, ini.getOriginalSpec());

        specCase.addClause(SIGNALS, ctxFor);
        specCase.addClause(SIGNALS, ini.getOriginalSpec());

        specCase.addClause(DIVERGES, JmlFacade.parseExpr("true"));

        ImmutableSet<Contract> resultList = createJMLOperationContracts(pm, specCase);
        assert resultList.size() == 1;
        Contract result = resultList.toArray(new Contract[1])[0];
        assert result instanceof FunctionalOperationContract;
        return ((FunctionalOperationContract) result);
    }

    private ImmutableList<LabeledParserRuleContext> createPrecond(IProgramMethod pm,
            LabeledParserRuleContext originalSpec) {
        ImmutableList<LabeledParserRuleContext> res = ImmutableSLList.nil();
        // TODO: add static invariant
        for (ParameterDeclaration p : pm.getMethodDeclaration().getParameters()) {
            if (!JMLInfoExtractor.parameterIsNullable(pm, p)) {
                final ImmutableSet<LabeledParserRuleContext> nonNullPositionedString =
                    JMLSpecExtractor.createNonNullPositionedString(
                        p.getVariableSpecification().getName(),
                        p.getVariableSpecification().getProgramVariable().getKeYJavaType(), false,
                        Location.fromToken(originalSpec.first.start),
                        services);
                res = res.append(nonNullPositionedString);
            }
        }
        return res;
    }
}
