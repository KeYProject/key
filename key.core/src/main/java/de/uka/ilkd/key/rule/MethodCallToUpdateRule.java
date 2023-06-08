package de.uka.ilkd.key.rule;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodOrConstructorReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Implements the rule which translates the formula
 * {@code [x = query(params);]post} to {@code { x := query(params) }post.}
 *
 * There are side conditions to be considered.
 *
 * @author Mattias Ulbrich
 */
public final class MethodCallToUpdateRule implements BuiltInRule {
    /**
     * Hint to refactor the final pre term.
     */
    public static final String FINAL_PRE_TERM_HINT = "finalPreTerm";

    /**
     * A static instance of the (built-in) operation contract rule application.
     */
    public static final MethodCallToUpdateRule INSTANCE = new MethodCallToUpdateRule();

    private static final Name NAME = new Name("Method Call to Update");

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private MethodCallToUpdateRule() {
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static Pair<ProgramVariable, MethodOrConstructorReference> getMethodCall(JavaBlock jb,
            Services services) {
        final ProgramVariable actualResult;
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
        } else if (activeStatement instanceof CopyAssignment) {
            final CopyAssignment ca = (CopyAssignment) activeStatement;
            final Expression lhs = ca.getExpressionAt(0);
            final Expression rhs = ca.getExpressionAt(1);
            if ((rhs instanceof MethodReference
                    || rhs instanceof New && ((New) rhs).getTypeDeclarationCount() == 0)
                    && lhs instanceof LocationVariable) {
                actualResult = (ProgramVariable) lhs;
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
        if (mr instanceof MethodReference) { // from MethodCall.java
            MethodReference methRef = (MethodReference) mr;
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

    private static Term getActualSelf(MethodOrConstructorReference mr, IProgramMethod pm,
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

    private static ImmutableList<Term> getActualParams(MethodOrConstructorReference mr,
            ExecutionContext ec, Services services) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (Expression expr : mr.getArguments()) {
            Term actualParam = services.getTypeConverter().convertToLogicElement(expr, ec);
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
        return getApplicableContracts(services, inst.pm, inst.staticType, inst.mod);
    }

    /**
     * Returns the operation contracts which are applicable for the passed operation and the passed
     * modality.
     *
     * @param services the services object
     * @param pm the program method
     * @param kjt the KeYJavaType of the class
     * @param modality the modality
     * @return all applicable contracts
     */
    private static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
            Services services, IProgramMethod pm, KeYJavaType kjt, Modality modality) {
        ImmutableSet<FunctionalOperationContract> result =
            services.getSpecificationRepository().getOperationContracts(kjt, pm, modality);

        // in box modalities, diamond contracts may be applied as well
        if (modality == Modality.BOX) {
            result = result.union(
                services.getSpecificationRepository().getOperationContracts(kjt, pm, Modality.DIA));
        } else if (modality == Modality.BOX_TRANSACTION) {
            result = result.union(services.getSpecificationRepository().getOperationContracts(kjt,
                pm, Modality.DIA_TRANSACTION));
        }

        return result;
    }

    private static PosInProgram getPosInProgram(JavaBlock jb) {
        ProgramElement pe = jb.program();

        PosInProgram result = PosInProgram.TOP;

        if (pe instanceof ProgramPrefix) {
            ProgramPrefix curPrefix = (ProgramPrefix) pe;

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

    private static StatementBlock replaceStatement(JavaBlock jb, StatementBlock replacement) {
        PosInProgram pos = getPosInProgram(jb);
        int lastPos = pos.last();
        ContextStatementBlockInstantiation csbi = new ContextStatementBlockInstantiation(pos,
            pos.up().down(lastPos + 1), null, jb.program());
        final NonTerminalProgramElement result = ProgramContextAdder.INSTANCE
                .start((JavaNonTerminalProgramElement) jb.program(), replacement, csbi);
        return (StatementBlock) result;
    }

    private static Instantiation instantiate(Term focusTerm, Services services) {
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
    public static Instantiation computeInstantiation(Term focusTerm, Services services) {
        // leading update?
        final Term u;
        final Term progPost;
        final TermBuilder tb = services.getTermBuilder();
        if (focusTerm.op() instanceof UpdateApplication) {
            u = UpdateApplication.getUpdate(focusTerm);
            progPost = UpdateApplication.getTarget(focusTerm);
        } else {
            u = tb.skip();
            progPost = focusTerm;
        }

        // focus (below update) must be modality term
        if (progPost.op() != Modality.BOX && progPost.op() != Modality.DIA
                && progPost.op() != Modality.BOX_TRANSACTION
                && progPost.op() != Modality.DIA_TRANSACTION) {
            return null;
        }
        final Modality mod = (Modality) progPost.op();

        // active statement must be method call or new
        final Pair<ProgramVariable, MethodOrConstructorReference> methodCall =
            getMethodCall(progPost.javaBlock(), services);
        if (methodCall == null) {
            return null;
        }
        final ProgramVariable actualResult = methodCall.first;
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
        final Term actualSelf = getActualSelf(mr, pm, ec, services);
        final ImmutableList<Term> actualParams = getActualParams(mr, ec, services);

        // cache and return result
        final Instantiation result =
            new Instantiation(u, progPost, mod, actualResult, actualSelf, staticType, mr, pm,
                actualParams, mod == Modality.DIA_TRANSACTION || mod == Modality.BOX_TRANSACTION);
        return result;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // focus must be top level succedent
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }

        // instantiation must succeed
        final Instantiation inst = instantiate(pio.subTerm(), goal.proof().getServices());
        if (inst == null) {
            return false;
        }

        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }

        // only applicable to strictly pure methods
        // TODO This should be extended to not only model methods ...
        if (!inst.pm.isModel()) {
            return false;
        }

        // TODO check that this is not a two-state model method.
        if (!(inst.actualResult instanceof ProgramVariable)) {
            return false;
        }

        return true;
    }

    @Nonnull
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
        final TermLabelState termLabelState = new TermLabelState();

        // get instantiation
        final Instantiation inst = instantiate(ruleApp.posInOccurrence().subTerm(), services);
        final JavaBlock jb = inst.progPost.javaBlock();
        final TermBuilder tb = services.getTermBuilder();

        // split goal into branches
        final ImmutableList<Goal> result;
        final Goal contGoal, nullGoal;
        final ReferencePrefix rp = inst.mr.getReferencePrefix();
        if (rp != null && !(rp instanceof ThisReference) && !(rp instanceof SuperReference)
                && !(rp instanceof TypeReference) && !(inst.pm.isStatic())) {
            result = goal.split(2);
            contGoal = result.tail().head();
            nullGoal = result.head();
            nullGoal.setBranchLabel("Null reference (" + inst.actualSelf + " = null)");
        } else {
            result = goal.split(1);
            contGoal = result.head();
            nullGoal = null;
        }
        contGoal.setBranchLabel("Assignment");

        // ---- create "Null Reference" branch
        if (nullGoal != null) {
            final Term actualSelfNotNull = tb.not(tb.equals(inst.actualSelf, tb.NULL()));
            nullGoal.changeFormula(new SequentFormula(tb.apply(inst.u, actualSelfNotNull, null)),
                ruleApp.posInOccurrence());
        }

        // ---- create "Assignment" cont branch
        StatementBlock postSB = replaceStatement(jb, new StatementBlock());
        JavaBlock postJavaBlock = JavaBlock.createJavaBlock(postSB);
        Term modTerm =
            tb.prog(inst.mod, postJavaBlock, inst.progPost.sub(0),
                TermLabelManager.instantiateLabels(termLabelState, services,
                    ruleApp.posInOccurrence(), this, ruleApp, contGoal, "PostModality", null,
                    inst.mod, new ImmutableArray<>(inst.progPost.sub(0)), null, postJavaBlock,
                    inst.progPost.getLabels()));
        Term lhs = tb.var(inst.actualResult);
        Term update = tb.elementary(lhs, makeCall(services, inst));
        Term normalPost = tb.apply(update, modTerm);
        contGoal.changeFormula(new SequentFormula(tb.apply(inst.u, normalPost, null)),
            ruleApp.posInOccurrence());

        TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(), this,
            nullGoal, null, null);

        return result;
    }

    private Term makeCall(Services services, Instantiation inst) {

        Term[] args = new Term[inst.pm.arity()];
        int idx = 0;

        if (inst.pm.argSort(0) == services.getTypeConverter().getHeapLDT().targetSort()) {
            args[idx++] = services.getTermBuilder().getBaseHeap();
        }

        if (!inst.pm.isStatic()) {
            args[idx++] = inst.actualSelf;
        }

        for (int i = 0; i < inst.actualParams.size(); i++) {
            args[idx++] = inst.actualParams.get(i);
        }

        return services.getTermFactory().createTerm(inst.pm, args);
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

    public static final class Instantiation {
        /**
         * The enclosing update term.
         */
        public final Term u;
        /**
         * The program post condition term.
         */
        public final Term progPost;
        /**
         * The modality.
         */
        public final Modality mod;
        /**
         * The actual result expression.
         */
        public final ProgramVariable actualResult;
        /**
         * The actual self term.
         */
        public final Term actualSelf;
        /**
         * The static KeYJavaType.
         */
        public final KeYJavaType staticType;
        /**
         * TODO
         */
        public final MethodOrConstructorReference mr;
        /**
         * The program method.
         */
        public final IProgramMethod pm;
        /**
         * The actual parameter terms.
         */
        public final ImmutableList<Term> actualParams;
        /**
         * TODO
         */
        public final boolean transaction;

        /**
         * Creates a new instantiation for the contract rule and the given variables.
         *
         * @param u the enclosing update term
         * @param progPost the post condition of the program method
         * @param mod the modality
         * @param actualResult the result expression
         * @param actualSelf the self term
         * @param staticType the static type
         * @param mr TODO
         * @param pm the program method
         * @param actualParams the actual parameter terms
         * @param transaction TODO
         */
        public Instantiation(Term u, Term progPost, Modality mod, ProgramVariable actualResult,
                Term actualSelf, KeYJavaType staticType, MethodOrConstructorReference mr,
                IProgramMethod pm, ImmutableList<Term> actualParams, boolean transaction) {
            assert u != null;
            assert u.sort() == Sort.UPDATE;
            assert progPost != null;
            assert progPost.sort() == Sort.FORMULA;
            assert mod != null;
            assert mr != null;
            assert pm != null;
            assert actualParams != null;
            this.u = u;
            this.progPost = progPost;
            this.mod = mod;
            this.actualResult = actualResult;
            this.actualSelf = actualSelf;
            this.staticType = staticType;
            this.mr = mr;
            this.pm = pm;
            this.actualParams = actualParams;
            this.transaction = transaction;
        }
    }

    public IBuiltInRuleApp createApp(PosInOccurrence pos) {
        return createApp(pos, null);
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }
}
