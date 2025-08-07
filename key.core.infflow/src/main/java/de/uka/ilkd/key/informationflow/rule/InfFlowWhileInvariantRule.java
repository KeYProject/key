/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule;

import java.util.Iterator;
import java.util.Objects;

import de.uka.ilkd.key.informationflow.*;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowLoopInvariantTacletBuilder;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class InfFlowWhileInvariantRule extends WhileInvariantRule {
    public static InfFlowWhileInvariantRule INSTANCE = new InfFlowWhileInvariantRule();

    @Override
    public ImmutableList<Goal> apply(Goal goal, final RuleApp ruleApp) throws RuleAbortException {
        return new InfFlowWhileInvariantRuleApplier(goal, (LoopInvariantBuiltInRuleApp<?>) ruleApp)
                .apply();
    }

    private static InfFlowData setUpInfFlowValidityGoal(Goal infFlowGoal,
            InfFlowLoopInvariantBuiltInRuleApp<?> ruleApp, Instantiation inst,
            JavaBlock guardJb,
            ImmutableSet<LocationVariable> localIns,
            ImmutableSet<LocationVariable> localOuts,
            ImmutableList<AnonUpdateData> anonUpdateDatas,
            JTerm anonUpdate,
            Services services) throws RuleAbortException {
        assert anonUpdateDatas.size() == 1 : "information flow " + "extension is at the "
            + "moment not compatible " + "with the non-base-heap " + "setting";
        final AnonUpdateData anonUpdateData = anonUpdateDatas.head();
        final TermBuilder tb = services.getTermBuilder();

        // reset validiy branch
        infFlowGoal.setBranchLabel("Information Flow Validity");

        // clear goal
        infFlowGoal.node().setSequent(JavaDLSequentKit.getInstance().getEmptySequent());
        infFlowGoal.clearAndDetachRuleAppIndex();

        // prepare data
        LoopSpecification inv = inst.inv();
        final JTerm guard = ruleApp.getGuard();
        InfFlowData infFlowData = prepareSetUpOfInfFlowValidityGoal(infFlowGoal, anonUpdateData,
            guard, inst, inv, services, ruleApp, localIns, localOuts, anonUpdate, guardJb);

        // generate information flow proof obligation variables
        final IFProofObligationVars ifVars =
            new IFProofObligationVars(infFlowData.symbExecVars, services);
        ruleApp.setInformationFlowProofObligationVars(ifVars);

        // set execution context
        ruleApp.setExecutionContext(inst.innermostExecutionContext());

        // create proof obligation
        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(inv, ifVars.c1, ifVars.c2,
            inst.innermostExecutionContext(), guard, services);
        final JTerm selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
        final JTerm post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);

        final JTerm finalTerm =
            tb.imp(tb.label(selfComposedExec, ParameterlessTermLabel.SELF_COMPOSITION_LABEL), post);
        ((InfFlowProof) infFlowGoal.proof()).addLabeledIFSymbol(selfComposedExec);
        infFlowGoal.addFormula(new SequentFormula(finalTerm), false, true);

        return infFlowData;
    }


    private static void setUpInfFlowPartOfUseGoal(InfFlowData infData, JTerm baseHeap,
            Goal goal, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final ProofObligationVars symbExecVars = infData.symbExecVars;
        final JTerm heapAtPreEq = tb.equals(symbExecVars.pre.heap, baseHeap);
        final JTerm heapAtPostEq = tb.equals(symbExecVars.post.heap, baseHeap);
        JTerm beforeAssumptions = tb.and(heapAtPreEq,
            tb.box(infData.guardJb, tb.equals(infData.guardAtPre, infData.guardTerm)));
        Iterator<JTerm> outsAtPre = infData.localOutsAtPre.iterator();
        for (JTerm locOut : infData.localOuts) {
            beforeAssumptions = tb.and(beforeAssumptions, tb.equals(outsAtPre.next(), locOut));
        }

        JTerm selfAtPostAssumption =
            // if the method is not static and if it is no constructor
            (symbExecVars.pre.self != null && symbExecVars.post.self != null) ?
            // then the self-variable does not change
                    tb.equals(symbExecVars.post.self, symbExecVars.pre.self) :
                    // else there is nothing to say about self
                    tb.tt();
        JTerm afterAssumptions = tb.and(heapAtPostEq,
            tb.box(infData.guardJb, tb.equals(infData.guardAtPost, infData.guardTerm)),
            selfAtPostAssumption);
        final Iterator<JTerm> outsAtPost = infData.localOutsAtPost.iterator();
        for (final JTerm locOut : infData.localOuts) {
            afterAssumptions = tb.and(afterAssumptions, tb.equals(outsAtPost.next(), locOut));
        }

        final JTerm infFlowAssumptions = tb.apply(infData.updates.first, tb.and(beforeAssumptions,
            tb.apply(infData.updates.second, tb.and(afterAssumptions, infData.applPredTerm))));

        goal.addFormula(new SequentFormula(infFlowAssumptions), true, false);
        goal.addTaclet(infData.infFlowApp, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        final InfFlowProof proof = (InfFlowProof) goal.proof();
        proof.addIFSymbol(infData.applPredTerm);
        proof.addIFSymbol(infData.infFlowApp);
        proof.addGoalTemplates(infData.infFlowApp);
    }


    private static InfFlowData prepareSetUpOfInfFlowValidityGoal(final Goal infFlowGoal,
            final AnonUpdateData anonUpdateData,
            final JTerm guardTerm, final Instantiation inst,
            LoopSpecification spec, Services services, LoopInvariantBuiltInRuleApp ruleApp,
            final ImmutableSet<LocationVariable> localIns,
            final ImmutableSet<LocationVariable> localOuts, final JTerm anonUpdate,
            final JavaBlock guardJb) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();
        final JTerm baseHeap = anonUpdateData.loopHeapAtPre();
        final JTerm selfTerm = inst.selfTerm();

        services.getSpecificationRepository().addLoopInvariant(spec);
        ruleApp.setLoopInvariant(spec);
        WhileInvariantRule.WhileInvariantRuleApplier.instantiate(ruleApp, services);

        // create heap_Before_LOOP
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Name heapAtPreName = new Name(tb.newName(baseHeap + "_Before_LOOP"));
        final Function heapAtPreFunc =
            new JFunction(heapAtPreName, heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(heapAtPreFunc);
        final JTerm heapAtPre = tb.func(heapAtPreFunc);

        final JTerm heapAtPost = anonUpdateData.loopHeap();
        final JTerm guardAtPre = buildBeforeVar(guardTerm, services);
        final JTerm guardAtPost = buildAfterVar(guardTerm, services);
        final JTerm selfAtPost = buildAtPostVar(selfTerm, "LOOP", services);
        // The set of local variables which are read in the loop body.
        final ImmutableList<JTerm> localInTerms = MiscTools.toTermList(localIns, tb);
        // The set of local variables which are written in the loop body.
        final ImmutableList<JTerm> localOutTerms = MiscTools.toTermList(localOuts, tb);
        // For every local variable which is written we need a pre and a post variable.
        final ImmutableList<JTerm> localOutsAtPre = buildLocalOutsAtPre(localOutTerms, services);
        final ImmutableList<JTerm> localOutsAtPost = buildLocalOutsAtPost(localOutTerms, services);
        // For every local variable which is read only, we need only a pre
        // variable (because the value of those variables does not change).
        // localIns contains the local variables which might be read in the
        // loop body, localOuts contains the local variables which might be
        // assigned. Both sets might overlap. Because we already generated
        // pre and post variables for all variables which might be assigned to,
        // additional pre variables need to be generated only for those variables
        // which are contained in localInTerms but not in localOutTerms.
        // Hence we have to filter out those local variables from localIns which
        // also appear in localOuts.
        final ImmutableList<JTerm> localInsWithoutOutDuplicates =
            MiscTools.filterOutDuplicates(localInTerms, localOutTerms);
        // The set of local pre variables is the union of the pre variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<JTerm> localVarsAtPre =
            localInsWithoutOutDuplicates.append(localOutsAtPre);
        // The set of local post variables is the union of the post variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<JTerm> localVarsAtPost =
            localInsWithoutOutDuplicates.append(localOutsAtPost);

        // generate proof obligation variables
        final StateVars instantiationPreVars =
            new StateVars(selfTerm, guardAtPre, localVarsAtPre, heapAtPre);
        final StateVars instantiationPostVars =
            new StateVars(selfAtPost, guardAtPost, localVarsAtPost, heapAtPost);
        final ProofObligationVars instantiationVars =
            new ProofObligationVars(instantiationPreVars, instantiationPostVars, services);

        // generate information flow invariant application predicate
        // and associated taclet
        final Pair<JTerm, JTerm> updates = new Pair<>(inst.u(), anonUpdate);
        final InfFlowLoopInvariantTacletBuilder ifInvariantBuilder =
            new InfFlowLoopInvariantTacletBuilder(services);
        ifInvariantBuilder.setInvariant(spec);
        ifInvariantBuilder.setExecutionContext(inst.innermostExecutionContext());
        ifInvariantBuilder.setContextUpdate(/* inst.u */);
        ifInvariantBuilder.setProofObligationVars(instantiationVars);
        ifInvariantBuilder.setGuard(guardTerm);

        final JTerm loopInvApplPredTerm = ifInvariantBuilder.buildContractApplPredTerm();
        final Taclet informationFlowInvariantApp = ifInvariantBuilder.buildTaclet(infFlowGoal);

        // return information flow data
        return new InfFlowData(instantiationVars, guardAtPre, guardAtPost,
            guardJb, guardTerm, localOutTerms, localOutsAtPre, localOutsAtPost, updates,
            loopInvApplPredTerm, informationFlowInvariantApp);
    }

    private static JTerm buildAtPostVar(JTerm varTerm, String suffix, Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = "_" + suffix;
        }
        final String name = tb.newName(varTerm + "_After" + suffix);
        final LocationVariable varAtPostVar =
            new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        return tb.var(varAtPostVar);
    }

    private static JTerm buildBeforeVar(JTerm varTerm, Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();
        final String name = tb.newName(varTerm + "_Before");
        final LocationVariable varAtPreVar =
            new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPreVar, services);
        return tb.var(varAtPreVar);
    }

    private static JTerm buildAfterVar(JTerm varTerm, Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();
        final String name = tb.newName(varTerm + "_After");
        final LocationVariable varAtPostVar =
            new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        return tb.var(varAtPostVar);
    }

    private static ImmutableList<JTerm> buildLocalOutsAtPre(ImmutableList<JTerm> varTerms,
            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JTerm> localOuts = ImmutableSLList.nil();
        for (final JTerm varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();

            final String name = tb.newName(varTerm + "_Before");
            final LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final JTerm varAtPost = tb.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    private static ImmutableList<JTerm> buildLocalOutsAtPost(ImmutableList<JTerm> varTerms,
            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JTerm> localOuts = ImmutableSLList.nil();
        for (final JTerm varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();

            final String name = tb.newName(varTerm + "_After");
            final LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final JTerm varAtPost = tb.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    static void register(ProgramVariable pv, Services services) {
        final Namespace<IProgramVariable> progVarNames =
            services.getNamespaces().programVariables();
        if (progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    public record InfFlowData(ProofObligationVars symbExecVars, JTerm guardAtPre,
            JTerm guardAtPost,
            JavaBlock guardJb,
            JTerm guardTerm, ImmutableList<JTerm> localOuts, ImmutableList<JTerm> localOutsAtPre,
            ImmutableList<JTerm> localOutsAtPost, Pair<JTerm, JTerm> updates, JTerm applPredTerm,
            Taclet infFlowApp) {
    }

    private class InfFlowWhileInvariantRuleApplier extends WhileInvariantRuleApplier {
        public InfFlowWhileInvariantRuleApplier(Goal goal, LoopInvariantBuiltInRuleApp<?> ruleApp) {
            super(goal, ruleApp);
        }

        @Override
        protected void prepareGoals(ImmutableList<Goal> result) {
            super.prepareGoals(result);

            Goal preserve = result.get(1);
            Goal terminate = result.get(2);
            if (InfFlowCheckInfo.isInfFlow(preserve) && inst.inv().hasInfFlowSpec(services)) {
                // set up information flow validity goal
                InfFlowData infFlowData = setUpInfFlowValidityGoal(preserve,
                    (InfFlowLoopInvariantBuiltInRuleApp<?>) ruleApp, inst, guardJb,
                    localIns, localOuts, anonUpdateDatas, anonUpdate, services);

                // set up information flow part of useGoal:
                // add infFlowAssumptions, add term and taclet to post goal
                setUpInfFlowPartOfUseGoal(infFlowData,
                    Objects.requireNonNull(anonUpdateDatas.head()).loopHeapAtPre(),
                    terminate,
                    services);
            }

        }
    }
}
