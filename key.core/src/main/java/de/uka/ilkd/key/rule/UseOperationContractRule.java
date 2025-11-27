/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.*;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public class UseOperationContractRule implements BuiltInRule {
    /**
     * Hint to refactor the final pre term.
     */
    public static final String FINAL_PRE_TERM_HINT = "finalPreTerm";

    /**
     * A static instance of the (built-in) operation contract rule application.
     */
    public static final UseOperationContractRule INSTANCE = new UseOperationContractRule();

    private static final Name NAME = new Name("Use Operation Contract");

    private static JTerm lastFocusTerm;
    private static Instantiation lastInstantiation;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected UseOperationContractRule() {
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static Pair<Expression, MethodOrConstructorReference> getMethodCall(JavaBlock jb,
            Services services) {
        final Expression actualResult;
        final MethodOrConstructorReference mr;

        final SourceElement activeStatement = JavaTools.getActiveStatement(jb);
        // active statement must be method reference or assignment with
        // method reference
        if (activeStatement instanceof MethodReference) {
            actualResult = null;
            mr = (MethodReference) activeStatement;
        } else if (activeStatement instanceof New
                && ((New) activeStatement).getTypeDeclarationCount() == 0) {
            actualResult = null;
            mr = (New) activeStatement;
        } else if (activeStatement instanceof CopyAssignment ca) {
            final Expression lhs = ca.getExpressionAt(0);
            final Expression rhs = ca.getExpressionAt(1);
            if ((rhs instanceof MethodReference
                    || rhs instanceof New && ((New) rhs).getTypeDeclarationCount() == 0)
                    && (lhs instanceof LocationVariable || lhs instanceof FieldReference)) {
                actualResult = lhs;
                mr = (MethodOrConstructorReference) rhs;
            } else {
                return null;
            }
        } else {
            return null;
        }

        // constructor may not refer to anonymous class
        if (mr instanceof New
                && ((New) mr).getTypeReference().getKeYJavaType()
                        .getJavaType() instanceof ClassDeclaration
                && ((ClassDeclaration) ((New) mr).getTypeReference().getKeYJavaType().getJavaType())
                        .isAnonymousClass()) {
            return null;
        }

        // receiver must be simple
        final ReferencePrefix rp = mr.getReferencePrefix();
        if (rp != null && !ProgramSVSort.SIMPLEEXPRESSION.canStandFor(rp, null, services)
                && !(rp instanceof ThisReference) && !(rp instanceof SuperReference)
                && !(rp instanceof TypeReference)) {
            return null;
        } else {
            return new Pair<>(actualResult, mr);
        }
    }

    private static KeYJavaType getStaticPrefixType(MethodOrConstructorReference mr,
            Services services, ExecutionContext ec) {
        if (mr instanceof MethodReference) {
            return ((MethodReference) mr).determineStaticPrefixType(services, ec);
        } else {
            New n = (New) mr;
            return n.getKeYJavaType(services, ec);
        }
    }

    private static IProgramMethod getProgramMethod(MethodOrConstructorReference mr,
            KeYJavaType staticType, ExecutionContext ec, Services services) {
        IProgramMethod result;
        if (mr instanceof MethodReference methRef) { // from MethodCall.java
            if (ec != null) {
                result = methRef.method(services, staticType, ec);
                if (result == null) {
                    // if a method is declared protected and prefix and
                    // execContext are in different packages we have to
                    // simulate visibility rules like being in prefixType
                    result = methRef.method(services, staticType,
                        methRef.getMethodSignature(services, ec), staticType);
                }
            } else {
                result = methRef.method(services, staticType,
                    methRef.getMethodSignature(services, ec), staticType);
            }
        } else {
            New n = (New) mr;
            ImmutableList<KeYJavaType> sig = ImmutableSLList.nil();
            for (Expression e : n.getArguments()) {
                sig = sig.append(e.getKeYJavaType(services, ec));
            }
            result = services.getJavaInfo().getConstructor(staticType, sig);
            assert result != null;
        }
        return result;
    }

    private static JTerm getActualSelf(MethodOrConstructorReference mr, IProgramMethod pm,
            ExecutionContext ec, Services services) {
        final TypeConverter tc = services.getTypeConverter();
        final ReferencePrefix rp = mr.getReferencePrefix();
        if (pm.isStatic() || pm.isConstructor()) {
            return null;
        } else if (rp == null || rp instanceof ThisReference || rp instanceof SuperReference) {
            return tc.findThisForSort(pm.getContainerType().getSort(), ec);
        } else if (rp instanceof FieldReference
                && ((FieldReference) rp).referencesOwnInstanceField()) {
            final ReferencePrefix rp2 =
                ((FieldReference) rp).setReferencePrefix(ec.getRuntimeInstance());
            return tc.convertToLogicElement(rp2);
        } else {
            return tc.convertToLogicElement(rp, ec);
        }
    }

    private static ImmutableList<JTerm> getActualParams(MethodOrConstructorReference mr,
            ExecutionContext ec, Services services) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (Expression expr : mr.getArguments()) {
            JTerm actualParam = services.getTypeConverter().convertToLogicElement(expr, ec);
            result = result.append(actualParam);
        }
        return result;
    }

    /**
     * Returns the operation contracts which are applicable for the passed instantiation.
     *
     * @param inst the operation contract rule instantiation
     * @param services the services object
     * @return all applicable contracts
     */
    public static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
            Instantiation inst, Services services) {
        if (inst == null) {
            return DefaultImmutableSet.nil();
        }

        // there must be applicable contracts for the operation
        return getApplicableContracts(services, inst.pm, inst.staticType, inst.modality.kind());
    }

    /**
     * Returns the operation contracts which are applicable for the passed operation and the passed
     * modality.
     *
     * @param services the services object
     * @param pm the program method
     * @param kjt the KeYJavaType of the class
     * @param modalityKind the modality
     * @return all applicable contracts
     */
    private static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
            Services services, IProgramMethod pm, KeYJavaType kjt,
            JModality.JavaModalityKind modalityKind) {
        ImmutableSet<FunctionalOperationContract> result =
            services.getSpecificationRepository().getOperationContracts(kjt, pm, modalityKind);

        // in box modalities, diamond contracts may be applied as well
        if (modalityKind == JModality.JavaModalityKind.BOX) {
            result = result.union(
                services.getSpecificationRepository().getOperationContracts(kjt, pm,
                    JModality.JavaModalityKind.DIA));
        } else if (modalityKind == JModality.JavaModalityKind.BOX_TRANSACTION) {
            result = result.union(services.getSpecificationRepository().getOperationContracts(kjt,
                pm, JModality.JavaModalityKind.DIA_TRANSACTION));
        }

        return result;
    }

    /**
     * @return (assumption, anon update, anon heap)
     */
    private static AnonUpdateData createAnonUpdate(LocationVariable heap, IProgramMethod pm,
            JTerm modifiable, Services services) {
        assert pm != null;
        assert modifiable != null;
        final TermBuilder tb = services.getTermBuilder();

        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final Name methodHeapName = new Name(tb.newName(heap + "After_" + pm.getName()));
        final Function methodHeapFunc =
            new JFunction(methodHeapName, heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(methodHeapFunc);
        final JTerm methodHeap = tb.func(methodHeapFunc);
        final Name anonHeapName = new Name(tb.newName("anon_" + heap + "_" + pm.getName()));
        final Function anonHeapFunc = new JFunction(anonHeapName, heap.sort());
        services.getNamespaces().functions().addSafely(anonHeapFunc);
        final JTerm anonHeap =
            tb.label(tb.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);
        final JTerm assumption = tb.equals(tb.anon(tb.var(heap), modifiable, anonHeap), methodHeap);
        final JTerm anonUpdate = tb.elementary(heap, methodHeap);

        return new AnonUpdateData(assumption, anonUpdate, methodHeap, tb.getBaseHeap(), anonHeap);
    }

    /**
     * Construct a free postcondition for the given method, i.e., a postcondition that is always
     * true as guaranteed by the Java language and is not required to be checked by the callee. For
     * constructors, it states that the self term is created and not null in the poststate and it
     * has not been created in the prestate. For regular methods, it states that the return value is
     * in range, meaning created or null for reference types, inInt(), etc., for integer types, and
     * for location sets containing only locations that belong to created objects.
     */
    private static JTerm getFreePost(List<LocationVariable> heapContext, IProgramMethod pm,
            KeYJavaType kjt, JTerm resultTerm, JTerm selfTerm,
            Map<LocationVariable, JTerm> heapAtPres,
            JTerm freeSpecPost, Services services) {
        final TermBuilder TB = services.getTermBuilder();
        final JTerm result;
        if (pm.isConstructor()) {
            assert resultTerm == null;
            assert selfTerm != null;
            JTerm createdForm = null;
            for (LocationVariable heap : heapContext) {
                if (heap == services.getTypeConverter().getHeapLDT().getSavedHeap()) {
                    continue;
                }
                final JTerm cr = TB.and(OpReplacer.replace(TB.var(heap), heapAtPres.get(heap),
                    TB.not(TB.created(TB.var(heap), selfTerm)), services.getTermFactory(),
                    services.getProof()), TB.created(TB.var(heap), selfTerm));
                if (createdForm == null) {
                    createdForm = cr;
                } else {
                    createdForm = TB.and(createdForm, cr);
                }
            }
            result = TB.and(TB.not(TB.equals(selfTerm, TB.NULL())), createdForm,
                TB.exactInstance(kjt.getSort(), selfTerm));
        } else if (resultTerm != null) {
            result = TB.reachableValue(resultTerm, pm.getReturnType());
        } else {
            result = TB.tt();
        }
        return TB.and(result, freeSpecPost);
    }

    private static PosInProgram getPosInProgram(JavaBlock jb) {
        ProgramElement pe = jb.program();

        PosInProgram result = PosInProgram.TOP;

        if (pe instanceof ProgramPrefix curPrefix) {

            final ImmutableArray<ProgramPrefix> prefix = curPrefix.getPrefixElements();
            final int length = prefix.size();

            // fail fast check
            curPrefix = prefix.get(length - 1); // length -1 >= 0 as prefix array
            // contains curPrefix as first element

            pe = curPrefix.getFirstActiveChildPos().getProgram(curPrefix);

            assert pe instanceof CopyAssignment || pe instanceof MethodReference
                    || pe instanceof New;

            int i = length - 1;
            do {
                result = curPrefix.getFirstActiveChildPos().append(result);
                i--;
                if (i >= 0) {
                    curPrefix = prefix.get(i);
                }
            } while (i >= 0);

        } else {
            assert pe instanceof CopyAssignment || pe instanceof MethodReference
                    || pe instanceof New;
        }
        return result;
    }

    public static StatementBlock replaceStatement(JavaBlock jb, StatementBlock replacement) {
        PosInProgram pos = getPosInProgram(jb);
        int lastPos = pos.last();
        ContextStatementBlockInstantiation csbi = new ContextStatementBlockInstantiation(pos,
            pos.up().down(lastPos + 1), null, jb.program());
        final NonTerminalProgramElement result = ProgramContextAdder.INSTANCE
                .start((JavaNonTerminalProgramElement) jb.program(), replacement, csbi);
        return (StatementBlock) result;
    }

    private static Instantiation instantiate(JTerm focusTerm, Services services) {
        // result cached?
        if (focusTerm == lastFocusTerm) {
            return lastInstantiation;
        }

        // compute
        final Instantiation result = computeInstantiation(focusTerm, services);

        // cache and return
        lastFocusTerm = focusTerm;
        lastInstantiation = result;
        return result;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Computes instantiation for contract rule on passed focus term. Internally only serves as
     * helper for instantiate().
     */
    public static @Nullable Instantiation computeInstantiation(
            JTerm focusTerm, Services services) {
        // leading update?
        final JTerm u;
        final JTerm progPost;
        final TermBuilder tb = services.getTermBuilder();
        if (focusTerm.op() instanceof UpdateApplication) {
            u = UpdateApplication.getUpdate(focusTerm);
            progPost = UpdateApplication.getTarget(focusTerm);
        } else {
            u = tb.skip();
            progPost = focusTerm;
        }

        // focus (below update) must be modality term
        if (!(progPost.op() instanceof JModality modality)) {
            return null;
        }

        // active statement must be method call or new
        final Pair<Expression, MethodOrConstructorReference> methodCall =
            getMethodCall(progPost.javaBlock(), services);
        if (methodCall == null) {
            return null;
        }
        final Expression actualResult = methodCall.first;
        final MethodOrConstructorReference mr = methodCall.second;
        assert mr != null;
        // arguments of method call must be simple expressions
        final ExecutionContext ec =
            JavaTools.getInnermostExecutionContext(progPost.javaBlock(), services);
        for (Expression arg : mr.getArguments()) {
            if (!ProgramSVSort.SIMPLEEXPRESSION.canStandFor(arg, ec, services)) {
                return null;
            }
        }

        // collect further information
        final KeYJavaType staticType = getStaticPrefixType(mr, services, ec);
        assert staticType != null;
        final IProgramMethod pm = getProgramMethod(mr, staticType, ec, services);
        assert pm != null : "Getting program method failed.\nReference: " + mr + ", static type: "
            + staticType + ", execution context: " + ec;
        final JTerm actualSelf = getActualSelf(mr, pm, ec, services);
        final ImmutableList<JTerm> actualParams = getActualParams(mr, ec, services);

        // cache and return result
        final Instantiation result =
            new Instantiation(u, progPost, modality, actualResult, actualSelf, staticType, mr, pm,
                actualParams, modality.<JModality.JavaModalityKind>kind().transaction());
        return result;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // focus must be top level succedent
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }

        // instantiation must succeed
        final Instantiation inst = instantiate((JTerm) pio.subTerm(), goal.proof().getServices());
        if (inst == null) {
            return false;
        }

        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }

        // cannot be applied on model methods
        if (inst.pm.isModel()) {
            return false;
        }

        // there must be applicable contracts for the operation
        final ImmutableSet<FunctionalOperationContract> contracts =
            getApplicableContracts(goal.proof().getServices(), inst.pm, inst.staticType,
                inst.modality.kind());
        if (contracts.isEmpty()) {
            return false;
        }

        // contract can be applied if modality is box and needs no termination
        // argument
        // see #1417, BOX_TRANSACTION added according to Wojciech's proposal.
        if (inst.modality.kind() == JModality.JavaModalityKind.BOX
                || inst.modality.kind() == JModality.JavaModalityKind.BOX_TRANSACTION) {
            return true;
        }

        // applying a contract here must not create circular dependencies
        // between proofs
        for (FunctionalOperationContract contract : contracts) {
            if (goal.proof().mgt().isContractApplicable(contract)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) {
        return new UseOperationContractRuleApplier(goal, ruleApp).apply();
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }

    @Override
    public String toString() {
        return displayName();
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    /**
     * @param u The enclosing update term.
     * @param progPost The program post condition term.
     * @param modality The modality.
     * @param actualResult The actual result expression.
     * @param actualSelf The actual self term.
     * @param staticType The static KeYJavaType.
     * @param mr TODO
     * @param pm The program method.
     * @param actualParams The actual parameter terms.
     * @param transaction TODO
     */
    public record Instantiation(JTerm u, JTerm progPost, JModality modality,
            Expression actualResult, JTerm actualSelf,
            KeYJavaType staticType, MethodOrConstructorReference mr, IProgramMethod pm,
            ImmutableList<JTerm> actualParams, boolean transaction) {
        /**
         * Creates a new instantiation for the contract rule and the given variables.
         *
         * @param u the enclosing update term
         * @param progPost the post condition of the program method
         * @param modality the modality
         * @param actualResult the result expression
         * @param actualSelf the self term
         * @param staticType the static type
         * @param mr TODO
         * @param pm the program method
         * @param actualParams the actual parameter terms
         * @param transaction TODO
         */
        public Instantiation {
            assert u != null;
            assert u.sort() == JavaDLTheory.UPDATE;
            assert progPost != null;
            assert progPost.sort() == JavaDLTheory.FORMULA;
            assert modality != null;
            assert mr != null;
            assert pm != null;
            assert actualParams != null;
        }
    }

    public ContractRuleApp createApp(PosInOccurrence pos) {
        return createApp(pos, null);
    }

    @Override
    public ContractRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new ContractRuleApp(this, pos);
    }

    /**
     * Returns the correct pre-heap variables.
     *
     * @param heapContext the heap variables
     * @param services the services object
     * @param inst the instantiation for the operation contract rule
     * @return a list of the resulting pre-heap variables
     */
    public static Map<LocationVariable, LocationVariable> computeAtPreVars(
            List<LocationVariable> heapContext, TermServices services, Instantiation inst) {
        return HeapContext.getBeforeAtPreVars(heapContext, services, "Before_" + inst.pm.getName());
    }

    /**
     * Returns the correct self term.
     *
     * @param baseHeapTerm the heap term
     * @param atPres the pre-heap variables as terms
     * @param baseHeap the heap variable
     * @param inst the instantiation for the operation contract rule
     * @param resultTerm the term of the result variable
     * @param tf the term factory
     * @return the resulting self term
     */
    public static JTerm computeSelf(JTerm baseHeapTerm, Map<LocationVariable, JTerm> atPres,
            LocationVariable baseHeap, Instantiation inst, JTerm resultTerm, TermFactory tf) {
        return OpReplacer.replace(baseHeapTerm, atPres.get(baseHeap),
            inst.pm.isConstructor() ? resultTerm : inst.actualSelf, tf);
    }

    /**
     * Returns the correct parameter terms.
     *
     * @param baseHeapTerm the heap term
     * @param atPres the pre-heap variables as terms
     * @param baseHeap the heap variable
     * @param inst the instantiation for the operation contract rule
     * @param tf the term factory
     * @return a list of the resulting parameter terms
     */
    public static ImmutableList<JTerm> computeParams(JTerm baseHeapTerm,
            Map<LocationVariable, JTerm> atPres, LocationVariable baseHeap, Instantiation inst,
            TermFactory tf) {
        return OpReplacer.replace(baseHeapTerm, atPres.get(baseHeap), inst.actualParams, tf);
    }

    /**
     * Computes the result variable for this instantiation.
     *
     * @param inst the instantiation for the operation contract rule
     * @param services the services object
     * @return the result variable
     */
    public static ProgramVariable computeResultVar(Instantiation inst, TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        return inst.pm.isConstructor() ? tb.selfVar(inst.staticType, true)
                : tb.resultVar(inst.pm, true);
    }

    /**
     * @param assumption The assumption term.
     * @param anonUpdate The anonymization update term.
     * @param methodHeap The heap term.
     * @param methodHeapAtPre The pre-heap term.
     * @param anonHeap The anonymization heap term.
     */
    protected record AnonUpdateData(JTerm assumption, JTerm anonUpdate, JTerm methodHeap,
            JTerm methodHeapAtPre,
            JTerm anonHeap) {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    protected static class UseOperationContractRuleApplier {
        private final Goal goal;
        private final RuleApp ruleApp;
        protected final Services services;

        protected Instantiation inst;
        protected TermLabelState termLabelState;
        protected JavaBlock jb;
        protected TermBuilder tb;
        protected List<LocationVariable> heapContext;
        protected Map<LocationVariable, LocationVariable> atPreVars;
        protected Map<LocationVariable, JTerm> atPres;
        protected ProgramVariable resultVar;
        protected ProgramVariable excVar;
        protected LocationVariable baseHeap;
        protected JTerm originalPost;
        protected JTerm pre;
        protected JTerm post;
        protected JTerm freeSpecPost;
        protected ImmutableList<JTerm> contractParams;
        protected JTerm contractSelf;
        protected FunctionalOperationContract contract;
        protected JTerm excPostAssumption;
        protected JTerm mby;
        protected JTerm excNull;
        protected JTerm excCreated;
        protected JTerm contractResult;
        protected JTerm freePost;
        protected JTerm freeExcPost;
        protected JTerm postAssumption;
        protected JTerm anonAssumption;
        protected JTerm anonUpdate;
        protected JTerm wellFormedAnon;
        protected JTerm atPreUpdates;
        protected JTerm reachableState;
        protected ImmutableList<AnonUpdateData> anonUpdateDatas = ImmutableSLList.nil();
        protected final Map<LocationVariable, JTerm> modifiables;
        protected final JTerm globalDefs;
        protected final JTerm originalPre;
        protected JTerm finalPreTerm;


        public UseOperationContractRuleApplier(Goal goal, RuleApp ruleApp) {
            this.goal = goal;
            this.ruleApp = ruleApp;
            termLabelState = new TermLabelState();
            services = goal.getOverlayServices();

            // get instantiation
            inst = instantiate((JTerm) ruleApp.posInOccurrence().subTerm(), services);
            jb = inst.progPost.javaBlock();
            tb = services.getTermBuilder();

            // configure contract
            contract = (FunctionalOperationContract) ((AbstractContractRuleApp<?>) ruleApp)
                    .getInstantiation();

            assert contract.getTarget().equals(inst.pm);

            heapContext =
                HeapContext.getModifiableHeaps(goal.proof().getServices(), inst.transaction);

            // prepare heapBefore_method
            atPreVars = computeAtPreVars(heapContext, services, inst);
            for (LocationVariable v : atPreVars.values()) {
                goal.addProgramVariable(v);
            }

            atPres = HeapContext.getAtPres(atPreVars, services);

            // create variables for result and exception
            resultVar = computeResultVar(inst, services);
            if (resultVar != null) {
                goal.addProgramVariable(resultVar);
            }
            assert inst.pm.isConstructor() || !(inst.actualResult != null && resultVar == null);
            excVar = tb.excVar(inst.pm, true);
            assert excVar != null;
            goal.addProgramVariable(excVar);

            baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
            // translate the contract
            final JTerm baseHeapTerm = tb.getBaseHeap();
            contractParams = computeParams(baseHeapTerm, atPres, baseHeap, inst, tb.tf());
            final JTerm contractResult =
                inst.pm.isConstructor() || resultVar == null ? null : tb.var(resultVar);
            contractSelf = computeSelf(baseHeapTerm, atPres, baseHeap, inst,
                contractResult == null && resultVar != null ? tb.var(resultVar) : contractResult,
                services.getTermFactory());
            Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
            for (LocationVariable h : heapContext) {
                heapTerms.put(h, tb.var(h));
            }
            globalDefs = contract.getGlobalDefs(baseHeap, baseHeapTerm, contractSelf,
                contractParams, services);
            originalPre = contract.getPre(heapContext, heapTerms, contractSelf, contractParams,
                atPres, services);
            pre = globalDefs == null ? originalPre : tb.apply(globalDefs, originalPre);
            originalPost = contract.getPost(heapContext, heapTerms, contractSelf,
                contractParams, contractResult, tb.var(excVar), atPres, services);
            JTerm originalFreePost = contract.getFreePost(heapContext, heapTerms, contractSelf,
                contractParams, contractResult, tb.var(excVar), atPres, services);
            originalFreePost = originalFreePost != null ? originalFreePost : tb.tt();
            post = globalDefs == null ? originalPost : tb.apply(globalDefs, originalPost);
            freeSpecPost =
                globalDefs == null ? originalFreePost : tb.apply(globalDefs, originalFreePost);
            modifiables = new LinkedHashMap<>();

            for (LocationVariable heap : heapContext) {
                final JTerm modifiable =
                    contract.getModifiable(heap, tb.var(heap), contractSelf, contractParams,
                        services);
                modifiables.put(heap, modifiable);
            }

            mby = contract.hasMby()
                    ? contract.getMby(heapTerms, contractSelf, contractParams, atPres, services)
                    : null;

            // prepare common stuff for the three branches
            for (LocationVariable heap : heapContext) {
                final AnonUpdateData tAnon;
                if (!contract.hasModifiable(heap)) {
                    tAnon = new AnonUpdateData(tb.tt(), tb.skip(), tb.var(heap), tb.var(heap),
                            tb.var(heap));
                } else {
                    tAnon = createAnonUpdate(heap, inst.pm, modifiables.get(heap), services);
                }
                anonUpdateDatas = anonUpdateDatas.append(tAnon);
                if (anonAssumption == null) {
                    anonAssumption = tAnon.assumption;
                } else {
                    anonAssumption = tb.and(anonAssumption, tAnon.assumption);
                }
                if (anonUpdate == null) {
                    anonUpdate = tAnon.anonUpdate;
                } else {
                    anonUpdate = tb.parallel(anonUpdate, tAnon.anonUpdate);
                }
                if (wellFormedAnon == null) {
                    wellFormedAnon = tb.wellFormed(tAnon.anonHeap);
                } else {
                    wellFormedAnon = tb.and(wellFormedAnon, tb.wellFormed(tAnon.anonHeap));
                }
                final JTerm up = tb.elementary(atPreVars.get(heap), tb.var(heap));
                if (atPreUpdates == null) {
                    atPreUpdates = up;
                } else {
                    atPreUpdates = tb.parallel(atPreUpdates, up);
                }
                if (reachableState == null) {
                    reachableState = tb.wellFormed(heap);
                } else {
                    reachableState = tb.and(reachableState, tb.wellFormed(heap));
                }
            }

            excNull = tb.equals(tb.var(excVar), tb.NULL());
            excCreated = tb.created(tb.var(excVar));
            freePost = getFreePost(heapContext, inst.pm, inst.staticType, contractResult,
                contractSelf, atPres, freeSpecPost, services);
            freeExcPost = inst.pm.isConstructor() ? freePost : tb.tt();
            postAssumption = tb.applySequential(new JTerm[] { inst.u, atPreUpdates },
                tb.and(anonAssumption,
                    tb.apply(anonUpdate, tb.and(excNull, freePost, post), null)));
            excPostAssumption = tb.applySequential(new JTerm[] { inst.u, atPreUpdates },
                tb.and(anonAssumption, tb.apply(anonUpdate,
                    tb.and(tb.not(excNull), excCreated, freeExcPost, post), null)));

        }

        public @NonNull ImmutableList<Goal> apply() {
            // split goal into three/four branches
            final ImmutableList<Goal> result;
            final Goal preGoal, postGoal, excPostGoal, nullGoal;
            final ReferencePrefix rp = inst.mr.getReferencePrefix();
            if (rp != null && !(rp instanceof ThisReference) && !(rp instanceof SuperReference)
                    && !(rp instanceof TypeReference) && !(inst.pm.isStatic())) {
                result = goal.split(4);
                postGoal = result.get(3);
                excPostGoal = result.get(2);
                preGoal = result.get(1);
                nullGoal = result.get(0);
            } else {
                result = goal.split(3);
                postGoal = result.get(2);
                excPostGoal = result.get(1);
                preGoal = result.get(0);
                nullGoal = null;
            }

            if (nullGoal != null) {
                nullGoal.setBranchLabel("Null reference (%s = null)".formatted(inst.actualSelf));
            }

            assert preGoal != null && postGoal != null && excPostGoal != null;
            preGoal.setBranchLabel("Pre (%s)".formatted(contract.getTarget().getName()));
            postGoal.setBranchLabel("Post (%s)".formatted(contract.getTarget().getName()));
            excPostGoal
                    .setBranchLabel(
                        "Exceptional Post (%s)".formatted(contract.getTarget().getName()));

            // create "Pre" branch
            if (nullGoal != null) {
                // see #1555
                reachableState = tb.and(reachableState, tb.created(contractSelf));
            }
            int i = 0;
            for (JTerm arg : contractParams) {
                KeYJavaType argKJT = contract.getTarget().getParameterType(i++);
                reachableState = tb.and(reachableState, tb.reachableValue(arg, argKJT));
            }

            finalPreTerm = getFinalPreTerm();
            finalPreTerm =
                TermLabelManager.refactorTerm(termLabelState, services, null, finalPreTerm,
                    ruleApp.rule(), preGoal, FINAL_PRE_TERM_HINT, null);
            createPreGoal(preGoal);
            createPostGoal(postGoal);
            createExceptionalPostGoal(excPostGoal);

            // create "Null Reference" branch
            if (nullGoal != null) {
                createNullGoal(nullGoal);
            }


            createRuleJustification();
            return result;
        }

        protected void createPreGoal(Goal preGoal) {
            preGoal.changeFormula(new SequentFormula(finalPreTerm), ruleApp.posInOccurrence());
            TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(),
                ruleApp.rule(),
                preGoal, null, null);
        }

        /// create and add {@link RuleJustificationBySpec}
        protected void createRuleJustification() {
            final RuleJustificationBySpec just = new RuleJustificationBySpec(contract);
            final ComplexRuleJustificationBySpec cjust =
                (ComplexRuleJustificationBySpec) goal.proof()
                        .getInitConfig().getJustifInfo().getJustification(ruleApp.rule());
            cjust.add(ruleApp, just);
        }

        protected void createNullGoal(Goal nullGoal) {
            final JTerm actualSelfNotNull = tb.not(tb.equals(inst.actualSelf, tb.NULL()));
            nullGoal.changeFormula(new SequentFormula(tb.apply(inst.u, actualSelfNotNull, null)),
                ruleApp.posInOccurrence());
            TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(),
                ruleApp.rule(), nullGoal, null, null);
        }


        protected void createExceptionalPostGoal(Goal excPostGoal) {
            // create "Exceptional Post" branch
            final StatementBlock excPostSB =
                replaceStatement(jb, new StatementBlock(new Throw(excVar)));
            JavaBlock excJavaBlock = JavaBlock.createJavaBlock(excPostSB);
            final JModality instantiatedModality =
                JModality.getModality(inst.modality.kind(), excJavaBlock);
            final JTerm originalExcPost = tb.apply(anonUpdate, tb.prog(instantiatedModality.kind(),
                instantiatedModality.programBlock(), inst.progPost.sub(0),
                TermLabelManager.instantiateLabels(termLabelState, services,
                    ruleApp.posInOccurrence(),
                    ruleApp.rule(), ruleApp, excPostGoal, "ExceptionalPostModality", null,
                    tb.tf().createTerm(instantiatedModality,
                        new ImmutableArray<>(inst.progPost.sub(0)), null,
                        inst.progPost.getLabels()))),
                null);
            final JTerm excPost =
                globalDefs == null ? originalExcPost : tb.apply(globalDefs, originalExcPost);
            excPostGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
            excPostGoal.changeFormula(new SequentFormula(tb.apply(inst.u, excPost, null)),
                ruleApp.posInOccurrence());
            excPostGoal.addFormula(new SequentFormula(excPostAssumption), true, false);
        }

        protected void createPostGoal(Goal postGoal) {
            // create "Post" branch
            final StatementBlock resultAssign;
            if (inst.actualResult == null) {
                resultAssign = new StatementBlock();
            } else {
                final CopyAssignment ca = new CopyAssignment(inst.actualResult, resultVar);
                resultAssign = new StatementBlock(ca);
            }
            final StatementBlock postSB = replaceStatement(jb, resultAssign);
            JavaBlock postJavaBlock = JavaBlock.createJavaBlock(postSB);
            JModality modality = JModality.getModality(inst.modality.kind(), postJavaBlock);
            final JTerm normalPost = tb.apply(anonUpdate,
                tb.prog(modality.kind(), modality.programBlock(), inst.progPost.sub(0),
                    TermLabelManager.instantiateLabels(termLabelState, services,
                        ruleApp.posInOccurrence(), ruleApp.rule(), ruleApp, postGoal,
                        "PostModality", null,
                        tb.tf().createTerm(modality,
                            new ImmutableArray<>(inst.progPost.sub(0)), null,
                            inst.progPost.getLabels()))),
                null);
            postGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
            postGoal.changeFormula(new SequentFormula(tb.apply(inst.u, normalPost, null)),
                ruleApp.posInOccurrence());
            postGoal.addFormula(new SequentFormula(postAssumption), true, false);
        }

        protected JTerm getFinalPreTerm() {
            JTerm finalPreTerm;
            final ContractPO po = services.getSpecificationRepository().getPOForProof(goal.proof());

            final JTerm mbyOk;
            // see #1417
            if (inst.modality.kind() != JModality.JavaModalityKind.BOX
                    && inst.modality.kind() != JModality.JavaModalityKind.BOX_TRANSACTION
                    && po != null
                    && mby != null) {
                // mbyOk = TB.and(TB.leq(TB.zero(services), mby, services),
                // TB.lt(mby, po.getMbyAtPre(), services));
                // mbyOk = TB.prec(mby, po.getMbyAtPre(), services);
                mbyOk = tb.measuredByCheck(mby);
            } else {
                mbyOk = tb.tt();
            }
            finalPreTerm = tb.applySequential(new JTerm[] { inst.u, atPreUpdates },
                tb.and(pre, reachableState, mbyOk));
            return finalPreTerm;
        }
    }
}
