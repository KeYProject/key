/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.util.Union;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * Implements the rule which translates the toplevel formula
 * {@code {U}[x = rec.query(params);]post} to
 * {@code {U}{ x := query(heap, rec, params) }post} for model methods.
 *
 * For model fields, it turns
 * {@code {U}[x = rec.query;]post} into
 * {@code {U}{ x := query(heap, rec) }post}.
 *
 * Currently this supports model methods and model fields which can only be
 * assigned to ghost entities.
 *
 * For strictly pure methods this is generally possible, but more side
 * conditions would arise: Ensuring termination, strict purity, precondition, ...
 *
 * TODO Extend this mechanism beyond model methods to strictly pure methods.
 *
 * @author Mattias Ulbrich
 */
public final class ObserverToUpdateRule implements BuiltInRule {
    /**
     * The single instance.
     */
    public static final ObserverToUpdateRule INSTANCE = new ObserverToUpdateRule();

    private static final Name NAME = new Name("Observer to update");

    /**
     * caching matching results
     */
    private static Term lastFocusTerm;
    private static Union<Instantiation, ModelFieldInstantiation> lastInstantiation;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private ObserverToUpdateRule() {
        // private for singleton pattern
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

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


    public IBuiltInRuleApp createApp(PosInOccurrence pos) {
        return createApp(pos, null);
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // focus must be top level succedent
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }

        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }

        // instantiation must succeed
        Union<Instantiation, ModelFieldInstantiation> inst =
            instantiate(pio.subTerm(), goal.proof().getServices());
        if (inst == null) {
            return false;
        }

        if (inst.isFirst()) {
            // additional checks for method calls.
            // currently only applicable to strictly pure methods
            if (!inst.getFirst().pm.isModel() || inst.getFirst().pm.getStateCount() > 1) {
                return false;
            }

            if (!(inst.getFirst().actualResult instanceof ProgramVariable)) {
                return false;
            }
        }

        return true;
    }

    @Nonnull
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
        Union<Instantiation, ModelFieldInstantiation> inst =
            instantiate(ruleApp.posInOccurrence().subTerm(), services);
        assert inst != null : "If isApplicable has been checked, this must not be null";
        if (inst.isFirst()) {
            return applyForMethods(goal, inst.getFirst(), services, ruleApp);
        } else {
            return applyForModelFields(goal, inst.getSecond(), services, ruleApp);
        }
    }


    // -----------------------------------
    // region application cases

    /*
     * Turn an assignment {U}[ x = obj.modelField; ... ]post into
     * {U}{ x := modelField(heap, obj) }[...]post.
     */
    private ImmutableList<Goal> applyForModelFields(Goal goal, ModelFieldInstantiation inst,
            Services services, RuleApp ruleApp) {
        final TermBuilder tb = services.getTermBuilder();
        final TermLabelState termLabelState = new TermLabelState();
        // split goal into branches
        final ImmutableList<Goal> result;
        final Goal contGoal, nullGoal;
        final ReferencePrefix rp = inst.fieldReference.getReferencePrefix();
        if (rp != null && !(rp instanceof ThisReference) && !(rp instanceof SuperReference)
                && !(rp instanceof TypeReference) && !(inst.modelField.isStatic())) {
            result = goal.split(2);
            contGoal = result.tail().head();
            nullGoal = result.head();
            nullGoal.setBranchLabel("Null reference (" + inst.receiver + " = null)");
        } else {
            result = goal.split(1);
            contGoal = result.head();
            nullGoal = null;
        }
        contGoal.setBranchLabel("Assignment");

        // ---- create "Null Reference" branch
        if (nullGoal != null) {
            final Term actualSelfNotNull = tb.not(tb.equals(inst.receiver, tb.NULL()));
            nullGoal.changeFormula(
                new SequentFormula(tb.apply(inst.update, actualSelfNotNull, null)),
                ruleApp.posInOccurrence());
        }

        // ---- create "Assignment" cont branch
        final JavaBlock jb = inst.modality.javaBlock();
        StatementBlock postSB = UseOperationContractRule.replaceStatement(jb, new StatementBlock());
        JavaBlock postJavaBlock = JavaBlock.createJavaBlock(postSB);
        Term modTerm =
            tb.prog((Modality) inst.modality.op(), postJavaBlock, inst.modality.sub(0),
                TermLabelManager.instantiateLabels(termLabelState, services,
                    ruleApp.posInOccurrence(), this, ruleApp, contGoal, "PostModality", null,
                    inst.modality.op(), inst.modality.subs(), null, postJavaBlock,
                    inst.modality.getLabels()));
        Term lhs = tb.var(inst.assignmentTarget);

        Term update = tb.elementary(lhs,
            makeCall(services, inst.observerSymbol, inst.receiver, ImmutableList.of()));
        Term normalPost = tb.apply(update, modTerm);
        contGoal.changeFormula(new SequentFormula(tb.apply(inst.update, normalPost, null)),
            ruleApp.posInOccurrence());

        TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(), this,
            nullGoal, null, null);

        return result;

    }

    /*
     * Turn an assignment {U}[ x = obj.modelMethod(params); ... ]post into
     * {U}{ x := modelMethod(heap, obj, params) }[...]post.
     */
    private ImmutableList<Goal> applyForMethods(Goal goal, Instantiation inst, Services services,
            RuleApp ruleApp) {
        final TermLabelState termLabelState = new TermLabelState();
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
        StatementBlock postSB = UseOperationContractRule.replaceStatement(jb, new StatementBlock());
        JavaBlock postJavaBlock = JavaBlock.createJavaBlock(postSB);
        Term modTerm =
            tb.prog(inst.mod, postJavaBlock, inst.progPost.sub(0),
                TermLabelManager.instantiateLabels(termLabelState, services,
                    ruleApp.posInOccurrence(), this, ruleApp, contGoal, "PostModality", null,
                    inst.mod, new ImmutableArray<>(inst.progPost.sub(0)), null, postJavaBlock,
                    inst.progPost.getLabels()));
        Term lhs = tb.var((ProgramVariable) inst.actualResult);
        Term update =
            tb.elementary(lhs, makeCall(services, inst.pm, inst.actualSelf, inst.actualParams));
        Term normalPost = tb.apply(update, modTerm);
        contGoal.changeFormula(new SequentFormula(tb.apply(inst.u, normalPost, null)),
            ruleApp.posInOccurrence());

        TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(), this,
            nullGoal, null, null);

        return result;
    }

    private Term makeCall(Services services, IObserverFunction op, Term receiver,
            ImmutableList<Term> methodArgs) {

        Term[] args = new Term[op.arity()];
        int idx = 0;

        if (op.argSort(0) == services.getTypeConverter().getHeapLDT().targetSort()) {
            args[idx++] = services.getTermBuilder().getBaseHeap();
        }

        if (!op.isStatic()) {
            args[idx++] = receiver;
        }

        for (int i = 0; i < methodArgs.size(); i++) {
            args[idx++] = methodArgs.get(i);
        }

        return services.getTermFactory().createTerm(op, args);
    }

    // endregion

    // -----------------------------------
    // region model field instantiation

    /**
     * Data structure to collect info when matching against a model field
     * retrieval.
     */
    private static class ModelFieldInstantiation {
        public FieldReference fieldReference;
        public Term update;
        public ProgramVariable modelField;
        public Term receiver;
        public ObserverFunction observerSymbol;
        LocationVariable assignmentTarget;
        Term modality;
    }

    /*
     * Fill a ModelFieldInstantiation by inspecting the focussed term.
     */
    private static ModelFieldInstantiation matchModelField(Term focusTerm, Services services) {

        // see UseOperationContractRule.doInstantiation
        ModelFieldInstantiation result = new ModelFieldInstantiation();

        // leading update?
        final Term mainFml;
        final TermBuilder tb = services.getTermBuilder();
        if (focusTerm.op() instanceof UpdateApplication) {
            result.update = UpdateApplication.getUpdate(focusTerm);
            mainFml = UpdateApplication.getTarget(focusTerm);
        } else {
            result.update = tb.skip();
            mainFml = focusTerm;
        }

        // focus (below update) must be modality term
        if (mainFml.op() != Modality.BOX && mainFml.op() != Modality.DIA
                && mainFml.op() != Modality.BOX_TRANSACTION
                && mainFml.op() != Modality.DIA_TRANSACTION) {
            return null;
        }
        result.modality = mainFml;

        // active statement must be reading model field
        final SourceElement activeStatement = JavaTools.getActiveStatement(mainFml.javaBlock());
        if (!(activeStatement instanceof CopyAssignment)) {
            return null;
        }

        final CopyAssignment ca = (CopyAssignment) activeStatement;
        final Expression lhs = ca.getExpressionAt(0);
        final Expression rhs = ca.getExpressionAt(1);

        if (!(lhs instanceof LocationVariable)) {
            return null;
        }
        result.assignmentTarget = (LocationVariable) lhs;

        if (!(rhs instanceof FieldReference)) {
            return null;
        }
        result.fieldReference = (FieldReference) rhs;
        result.modelField = result.fieldReference.getProgramVariable();

        if (!result.modelField.isModel()) {
            return null;
        }

        // find receiver term
        final ExecutionContext ec =
            JavaTools.getInnermostExecutionContext(mainFml.javaBlock(), services);
        final TypeConverter tc = services.getTypeConverter();
        final ReferencePrefix rp = result.fieldReference.getReferencePrefix();
        if (!result.modelField.isStatic()) {
            if (rp == null || rp instanceof ThisReference || rp instanceof SuperReference) {
                result.receiver =
                    tc.findThisForSort(result.modelField.getContainerType().getSort(), ec);
            } else if (rp instanceof FieldReference
                    && ((FieldReference) rp).referencesOwnInstanceField()) {
                final ReferencePrefix rp2 =
                    ((FieldReference) rp).setReferencePrefix(ec.getRuntimeInstance());
                result.receiver = tc.convertToLogicElement(rp2);
            } else {
                result.receiver = tc.convertToLogicElement(rp, ec);
            }
        }

        // find the observer symbol
        result.observerSymbol =
            (ObserverFunction) services.getTypeConverter().getHeapLDT()
                    .getFieldSymbolForPV((LocationVariable) result.modelField, services);

        return result;

    }

    private static Union<Instantiation, ModelFieldInstantiation> instantiate(Term focusTerm,
            Services services) {
        // result cached?
        if (focusTerm == lastFocusTerm) {
            return lastInstantiation;
        }

        // compute
        Instantiation inst = UseOperationContractRule.computeInstantiation(focusTerm, services);
        if (inst != null) {
            lastInstantiation = Union.fromFirst(inst);
        } else {
            ModelFieldInstantiation mfInst = matchModelField(focusTerm, services);
            if (mfInst != null) {
                lastInstantiation = Union.fromSecond(mfInst);
            } else {
                lastInstantiation = null;
            }
        }

        // cache and return
        lastFocusTerm = focusTerm;
        return lastInstantiation;
    }
    // endregion

}
