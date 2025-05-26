/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.RustTools;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.ast.visitor.ProgramContextAdder;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.UpdateApplication;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.mgt.ComplexRuleJustificationBySpec;
import org.key_project.rusty.proof.mgt.RuleJustificationBySpec;
import org.key_project.rusty.rule.inst.ContextBlockExpressionInstantiation;
import org.key_project.rusty.speclang.FunctionalOperationContract;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public final class UseOperationContractRule implements BuiltInRule {
    /**
     * A static instance of the (built-in) operation contract rule application.
     */
    public static final UseOperationContractRule INSTANCE = new UseOperationContractRule();

    private static final Name NAME = new Name("Use Operation Contract");

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private UseOperationContractRule() {
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static ResultAndCall getMethodCall(RustyBlock rb,
            Services services) {
        final Expr actualResult;final Call call;

        final RustyProgramElement activeExpr=RustTools.getActiveExpr(rb);
        // active expr must be function call, method call or assignment with
        // function/method call
        switch(activeExpr){case CallExpression ce->{actualResult=null;call=ce;}case MethodCallExpression me->{actualResult=null;call=me;}case AssignmentExpression as->{final Expr lhs=as.lhs();final Expr rhs=as.rhs();if((rhs instanceof Call c)&&(lhs instanceof ProgramVariable)){actualResult=lhs;call=c;}else{return null;}}case null,default->{return null;}}

        // receiver must be simple
        if(call instanceof MethodCallExpression me&&!ProgramSVSort.SIMPLE_EXPRESSION.canStandFor(me.callee(),services)){return null;}else{return new ResultAndCall(actualResult,call);}
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

    private static ProgramFunction getFunction(Call call, Services services) {
        ProgramFunction result;
        if (call instanceof CallExpression ce) {
            result = ce.function(services);
            if (result == null) {
                throw new RuntimeException("TODO @ DD: Could not find function in UseOpContract");
            }
        } else {
            // Method call
            throw new RuntimeException("TODO @ DD: Method calls in UseOpContract");
        }
        return result;
    }

    private static Term getActualSelf(Call call, ProgramFunction fn,
            Services services) {
        Expr callee = call.callee();
        if (fn.getFunction().selfKind() == Function.ImplicitSelfKind.None) {
            return null;
        } else {
            // TODO
            throw new RuntimeException("TODO @ DD: Method self");
        }
    }

    private static ImmutableList<Term> getActualParams(Call call, Services services) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (var expr : call.params()) {
            Term actualParam = services.convertToLogicElement(expr);
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
        return getApplicableContracts(services, inst.fn, inst.modality.kind());
    }

    /**
     * Returns the operation contracts which are applicable for the passed operation and the passed
     * modality.
     *
     * @param services the services object
     * @param fn the program method
     * @param modalityKind the modality
     * @return all applicable contracts
     */
    private static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
            Services services, ProgramFunction fn,
            Modality.RustyModalityKind modalityKind) {
        ImmutableSet<FunctionalOperationContract> result =
            services.getSpecificationRepository().getOperationContracts(fn, modalityKind);

        // in box modalities, diamond contracts may be applied as well
        if (modalityKind == Modality.RustyModalityKind.BOX) {
            result = result.union(
                services.getSpecificationRepository().getOperationContracts(fn,
                    Modality.RustyModalityKind.DIA));
        }

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
        if (!(progPost.op() instanceof Modality modality)) {
            return null;
        }

        // active statement must be method call or new
        final var methodCall =
            getMethodCall(modality.program(), services);
        if (methodCall == null) {
            return null;
        }
        final Expr actualResult = methodCall.result();
        final Call call = methodCall.call();
        assert call != null;
        // arguments of method call must be simple expressions
        for (var arg : call.params()) {
            if (!ProgramSVSort.SIMPLE_EXPRESSION.canStandFor(arg, services)) {
                return null;
            }
        }

        // collect further information
        final ProgramFunction fn = getFunction(call, services);
        assert fn != null : "Getting program method failed.\nReference: " + call;
        final Term actualSelf = getActualSelf(call, fn, services);
        final ImmutableList<Term> actualParams = getActualParams(call, services);

        // cache and return result
        final Instantiation result =
            new Instantiation(u, progPost, modality, actualResult, actualSelf, call, fn,
                actualParams);
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
        // if (Transformer.inTransformer(pio)) {
        // return false;
        // }

        // there must be applicable contracts for the operation
        final ImmutableSet<FunctionalOperationContract> contracts =
            getApplicableContracts(goal.proof().getServices(), inst.fn,
                inst.modality.kind());
        if (contracts.isEmpty()) {
            return false;
        }

        // contract can be applied if modality is box and needs no termination
        // argument
        if (inst.modality.kind() == Modality.RustyModalityKind.BOX) {
            return true;
        }

        // applying a contract here must not create circular dependencies
        // between proofs
        for (var contract : contracts) {
            if (goal.proof().mgt().isContractApplicable(contract)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public ContractRuleApp createApp(PosInOccurrence pos, Services services) {
        return new ContractRuleApp(this, pos);
    }

    public ContractRuleApp createApp(PosInOccurrence pos) {
        return createApp(pos, null);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp)
            throws RuleAbortException {
        var services = goal.getOverlayServices();
        // get instantiation
        final Instantiation inst = instantiate(ruleApp.posInOccurrence().subTerm(), services);
        final RustyBlock rb = inst.modality().program();
        final TermBuilder tb = services.getTermBuilder();

        final var contract =
            (FunctionalOperationContract) ((AbstractContractRuleApp) ruleApp).getInstantiation();
        assert contract.getTarget().equals(inst.fn);

        // create variables for result
        final ProgramVariable resultVar = computeResultVar(inst, services);
        assert resultVar != null;
        goal.addProgramVariable(resultVar);

        final ImmutableList<Term> contractParams = inst.actualParams;
        final Term contractResult = tb.var(resultVar);
        // TODO: self
        final Term globalDefs = contract.getGlobalDefs();
        final Term originalPre = contract.getPre(null, contractParams, services);
        final Term pre = globalDefs == null ? originalPre : tb.apply(globalDefs, originalPre);
        final Term originalPost = contract.getPost(null, contractParams, contractResult, services);
        final Term post = globalDefs == null ? originalPost : tb.apply(globalDefs, originalPost);
        final Term modifiable = contract.getModifiable(null, contractParams, services);

        final Term mby = contract.hasMby() ? contract.getMby() : null;

        // split goal into two branches
        final ImmutableList<Goal> result = goal.split(2);
        final Goal preGoal = result.head();
        final Goal postGoal = result.tail().head();

        preGoal.setBranchLabel("Pre (" + contract.getTarget().name() + ")");
        postGoal.setBranchLabel("Post (" + contract.getTarget().name() + ")");

        // prepare common stuff for the three branches
        Term reachableState = null;

        Term postAssumption = tb.apply(inst.u, post);

        // create "Pre" branch
        int i = 0;
        for (Term arg : contractParams) {
            final KeYRustyType argKRT = contract.getTarget().getParamType(i++);
            final Term reachable = tb.reachableValue(arg, argKRT);
            if (reachableState == null) {
                reachableState = reachable;
            } else {
                reachableState = tb.and(reachableState, reachable);
            }
        }

        // TODO: mby
        final Term finalPreTerm = tb.apply(inst.u, tb.and(pre, reachableState));
        preGoal.changeFormula(new SequentFormula(finalPreTerm), ruleApp.posInOccurrence());

        // create "Post" branch
        final ContextBlockExpression resultAssign;
        if (inst.actualResult == null) {
            resultAssign = new ContextBlockExpression(ImmutableList.of(), TupleExpression.UNIT);
        } else {
            resultAssign = new ContextBlockExpression(ImmutableList.of(),
                new AssignmentExpression(inst.actualResult, resultVar));
        }
        final BlockExpression postBE = replaceBlock(rb, resultAssign);
        final RustyBlock postRustyBlock = new RustyBlock(postBE);
        Modality modality = Modality.getModality(inst.modality.kind(), postRustyBlock);
        final Term normalPost = tb.prog(modality.kind(), modality.program(), inst.progPost.sub(0));
        postGoal.changeFormula(new SequentFormula(tb.apply(inst.u, normalPost)),
            ruleApp.posInOccurrence());
        postGoal.addFormula(new SequentFormula(postAssumption), true, false);

        // create justification
        final RuleJustificationBySpec just = new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cJust = (ComplexRuleJustificationBySpec) goal.proof()
                .getInitConfig().getJustifInfo().getJustification(this);
        cJust.add(ruleApp, just);

        return result;
    }

    /**
     * Computes the result variable for this instantiation.
     *
     * @param inst the instantiation for the operation contract rule
     * @param services the services object
     * @return the result variable
     */
    public static ProgramVariable computeResultVar(Instantiation inst, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.resultVar(inst.fn, true);
    }

    private static PosInProgram getPosInProgram(RustyBlock rb) {
        var pe = rb.program();

        var result = PosInProgram.TOP;

        if (pe instanceof PossibleProgramPrefix currPrefix) {
            final var prefix = currPrefix.getPrefixElements();
            final int length = prefix.size();

            // fail fast check
            currPrefix = prefix.get(length - 1); // length -1 >= 0 as prefix array
            // contains curPrefix as first element

            pe = currPrefix.getFirstActiveChildPos().getProgram(currPrefix);

            assert pe instanceof AssignmentExpression;

            int i = length - 1;
            do {
                result = currPrefix.getFirstActiveChildPos().append(result);
                i--;
                if (i >= 0) {
                    currPrefix = prefix.get(i);
                }
            } while (i >= 0);
        } else {
            assert pe instanceof AssignmentExpression;
        }
        return result;
    }

    public BlockExpression replaceBlock(RustyBlock rb, ContextBlockExpression replacement) {
        PosInProgram pos = getPosInProgram(rb);
        int lastPos = pos.last();
        ContextBlockExpressionInstantiation cbei =
            new ContextBlockExpressionInstantiation(pos, pos.up().down(lastPos + 1), rb.program());
        return (BlockExpression) ProgramContextAdder.INSTANCE.start(rb.program(), replacement,
            cbei);
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
     * @param u            The enclosing update term.
     * @param progPost     The program post condition term.
     * @param modality     The modality.
     * @param actualResult The actual result expression.
     * @param actualSelf   The actual self term.
     * @param call         The call expression
     * @param fn           The program function.
     * @param actualParams The actual parameter terms.
     */
    public record Instantiation(Term u, Term progPost, Modality modality, Expr actualResult, Term actualSelf,
                                Call call, ProgramFunction fn,
                                ImmutableList<Term> actualParams) {
        /**
         * Creates a new instantiation for the contract rule and the given variables.
         *
         * @param u            the enclosing update term
         * @param progPost     the post condition of the program method
         * @param modality     the modality
         * @param actualResult the result expression
         * @param actualSelf   the self term
         * @param call         the call expression
         * @param fn           the program method
         * @param actualParams the actual parameter terms
         */
        public Instantiation {
            assert u != null;
            assert u.sort() == RustyDLTheory.UPDATE;
            assert progPost != null;
            assert progPost.sort() == RustyDLTheory.FORMULA;
            assert modality != null;
            assert call != null;
            assert fn != null;
            assert actualParams != null;
        }
    }

    private record ResultAndCall(@Nullable Expr result, Call call) {
    }
}
