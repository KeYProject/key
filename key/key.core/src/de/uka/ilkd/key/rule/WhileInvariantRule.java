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

package de.uka.ilkd.key.rule;

import java.util.Iterator;
import java.util.List;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowLoopInvariantTacletBuilder;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvariantTransformer;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.LoopWellDefinedness;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * The "classic" loop invariant rule with three goals "Invariant Initially
 * Valid", "Body Preserves Invariant" and "Use Case".
 * 
 * @deprecated
 *             <p>
 *             This rule is deprecated; consider using
 *             {@link LoopScopeInvariantRule} instead. The sequents created by
 *             the {@link WhileInvariantRule} are badly readable; furthermore,
 *             there were several soundness issues in the past that induced some
 *             quickly hacked-in fixes. The {@link LoopScopeInvariantRule}
 *             offers a better treatment of complex loop behavior including
 *             exceptions etc.
 *             </p>
 *             <p>
 *             However, this is the only rule that currently supports
 *             information flow proof obligations, Java Card transactions and
 *             the "wellformed"-check. The new rule should be extended by this
 *             in the near future.
 *             </p>
 */
public final class WhileInvariantRule extends AbstractLoopInvariantRule {
    /**
     * The hint used to refactor the initial invariant.
     */
    public static final String INITIAL_INVARIANT_ONLY_HINT = "onlyInitialInvariant";

    /**
     * The unit used to refactor the full invariant.
     */
    public static final String FULL_INVARIANT_TERM_HINT = "fullInvariant";

    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();

    private static final Name NAME = new Name("Loop Invariant");

    public static final String BODY_PRESERVES_INVARIANT_LABEL = "Body Preserves Invariant";

    @Override
    public int getNrOfGoals() {
        return WellDefinednessCheck.isOn() ? 4 : 3;
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        // Initial assertions
        assert ruleApp instanceof LoopInvariantBuiltInRuleApp;

        LoopInvariantInformation loopInvInfo = doPreparations(goal, services,
                ruleApp);

        final ImmutableList<Goal> goals = loopInvInfo.goals;

        Goal wdGoal;
        if (WellDefinednessCheck.isOn()) {
            wdGoal = goals.tail().tail().tail().head();
            wdGoal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
        } else {
            wdGoal = null;
        }

        Goal initGoal = goals.tail().tail().head();
        Goal bodyGoal = goals.tail().head();
        Goal useGoal = goals.head();

        final KeYJavaType booleanKJT = loopInvInfo.services.getTypeConverter()
                .getBooleanType();

        List<LocationVariable> heapContext = ((IBuiltInRuleApp) loopInvInfo.ruleApp)
                .getHeapContext();

        // "Invariant Initially Valid":
        // \replacewith (==> inv );
        prepareInvInitiallyValidBranch(loopInvInfo.termLabelState,
                loopInvInfo.services, loopInvInfo.ruleApp, loopInvInfo.inst,
                loopInvInfo.invTerm, loopInvInfo.reachableState, initGoal);
        // TODO Jonas: Ist die Doppelanwendung nötig?

        final ImmutableSet<ProgramVariable> localIns = MiscTools
                .getLocalIns(loopInvInfo.inst.loop, loopInvInfo.services);
        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(loopInvInfo.inst.loop, loopInvInfo.services);

        setupWdGoal(wdGoal, loopInvInfo.inst.inv, loopInvInfo.inst.u,
                loopInvInfo.inst.selfTerm, heapContext.get(0),
                loopInvInfo.anonUpdateData.head().anonHeap, localIns,
                loopInvInfo.ruleApp.posInOccurrence(), loopInvInfo.services);

        // prepare guard
        final Triple<JavaBlock, Term, Term> guardStuff = prepareGuard(
                loopInvInfo.inst, booleanKJT, loopInvInfo.ruleApp,
                loopInvInfo.services);
        final JavaBlock guardJb = guardStuff.first;
        final Term guardTrueTerm = guardStuff.second;
        final Term guardFalseTerm = guardStuff.third;

        // "Body Preserves Invariant":
        // \replacewith (==> #atPreEqs(anon1)
        // -> #introNewAnonUpdate(#modifies, #locDepFunc(anon1, \[{.. while (#e)
        // #s ...}\]post) & inv ->
        // (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
        // #whileInvRule(\[{.. while (#e) #s ...}\]post,
        // #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post)
        // & inv)),
        // anon1));
        prepareBodyPreservesBranch(loopInvInfo.termLabelState,
                loopInvInfo.services, loopInvInfo.ruleApp,
                loopInvInfo.goal.sequent(), loopInvInfo.inst,
                loopInvInfo.invTerm, loopInvInfo.wellFormedAnon,
                loopInvInfo.frameCondition, loopInvInfo.variantPO, bodyGoal,
                guardJb, guardTrueTerm, loopInvInfo.uBeforeLoopDefAnonVariant,
                loopInvInfo.uAnonInv);

        if (InfFlowCheckInfo.isInfFlow(loopInvInfo.goal)
                && loopInvInfo.inst.inv.hasInfFlowSpec(loopInvInfo.services)) {
            // set up information flow validity goal
            InfFlowData infFlowData;
            try {
                infFlowData = setUpInfFlowValidityGoal(bodyGoal,
                        loopInvInfo.ruleApp, loopInvInfo.inst, guardJb,
                        localIns, localOuts, loopInvInfo.anonUpdateData,
                        loopInvInfo.anonUpdate, loopInvInfo.services);

                // set up information flow part of useGoal:
                // add infFlowAssumptions, add term and taclet to post goal
                setUpInfFlowPartOfUseGoal(infFlowData,
                        loopInvInfo.anonUpdateData.head().loopHeapAtPre,
                        useGoal, loopInvInfo.services);
            } catch (RuleAbortException e) {
                throw new RuntimeException(e);
            }
        }

        // "Invariant Initially Valid":
        // \replacewith (==> inv );
        prepareInvInitiallyValidBranch(loopInvInfo.termLabelState,
                loopInvInfo.services, loopInvInfo.ruleApp, loopInvInfo.inst,
                loopInvInfo.invTerm, loopInvInfo.reachableState, initGoal);

        setupWdGoal(wdGoal, loopInvInfo.inst.inv, loopInvInfo.inst.u,
                loopInvInfo.inst.selfTerm, heapContext.get(0),
                loopInvInfo.anonUpdateData.head().anonHeap, localIns,
                loopInvInfo.ruleApp.posInOccurrence(), loopInvInfo.services);

        // "Use Case":
        // \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
        // (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
        // (#v1=FALSE -> \[{.. ...}\]post)),anon2))
        final Term[] uAnon = new Term[] { loopInvInfo.inst.u,
                loopInvInfo.anonUpdate };
        prepareUseCaseBranch(loopInvInfo.termLabelState, loopInvInfo.services,
                loopInvInfo.ruleApp, loopInvInfo.inst,
                loopInvInfo.wellFormedAnon, useGoal, guardJb, guardFalseTerm,
                uAnon, loopInvInfo.uAnonInv);

        return goals;
    }

    private static InfFlowData prepareSetUpOfInfFlowValidityGoal(
            final AnonUpdateData anonUpdateData, final Term guardTerm,
            final Instantiation inst, LoopSpecification spec, Services services,
            LoopInvariantBuiltInRuleApp ruleApp,
            final ImmutableSet<ProgramVariable> localIns,
            final ImmutableSet<ProgramVariable> localOuts,
            final Term anonUpdate, final JavaBlock guardJb)
            throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();
        final Term baseHeap = anonUpdateData.loopHeapAtPre;
        final Term selfTerm = inst.selfTerm;

        services.getSpecificationRepository().addLoopInvariant(spec);
        ruleApp.setLoopInvariant(spec);
        instantiate(ruleApp, services);

        // create heap_Before_LOOP
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Name heapAtPreName = new Name(tb.newName(baseHeap + "_Before_LOOP"));
        final Function heapAtPreFunc = new Function(heapAtPreName,
                heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(heapAtPreFunc);
        final Term heapAtPre = tb.func(heapAtPreFunc);

        final Term heapAtPost = anonUpdateData.loopHeap;
        final Term guardAtPre = buildBeforeVar(guardTerm, services);
        final Term guardAtPost = buildAfterVar(guardTerm, services);
        final Term selfAtPost = buildAtPostVar(selfTerm, "LOOP", services);
        // The set of local variables which are read in the loop body.
        final ImmutableList<Term> localInTerms = MiscTools.toTermList(localIns,
                tb);
        // The set of local variables which are written in the loop body.
        final ImmutableList<Term> localOutTerms = MiscTools
                .toTermList(localOuts, tb);
        // For every local variable which is written we need a pre and a post
        // variable.
        final ImmutableList<Term> localOutsAtPre = buildLocalOutsAtPre(
                localOutTerms, services);
        final ImmutableList<Term> localOutsAtPost = buildLocalOutsAtPost(
                localOutTerms, services);
        // For every local variable which is read only, we need only a pre
        // variable (because the value of those variables does not change).
        // localIns contains the local variables which might be read in the
        // loop body, localOuts contains the local variables which might be
        // assigned. Both sets might overlap. Because we already generated
        // pre and post variables for all variables which might be assigned to,
        // additional pre variables need to be generated only for those
        // variables
        // which are contained in localInTerms but not in localOutTerms.
        // Hence we have to filter out those local variables from localIns which
        // also appear in localOuts.
        final ImmutableList<Term> localInsWithoutOutDuplicates = MiscTools
                .filterOutDuplicates(localInTerms, localOutTerms);
        // The set of local pre variables is the union of the pre variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<Term> localVarsAtPre = localInsWithoutOutDuplicates
                .append(localOutsAtPre);
        // The set of local post variables is the union of the post variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<Term> localVarsAtPost = localInsWithoutOutDuplicates
                .append(localOutsAtPost);

        // generate proof obligation variables
        final StateVars instantiationPreVars = new StateVars(selfTerm,
                guardAtPre, localVarsAtPre, heapAtPre);
        final StateVars instantiationPostVars = new StateVars(selfAtPost,
                guardAtPost, localVarsAtPost, heapAtPost);
        final ProofObligationVars instantiationVars = new ProofObligationVars(
                instantiationPreVars, instantiationPostVars, services);

        // generate information flow invariant application predicate
        // and associated taclet
        final Pair<Term, Term> updates = new Pair<Term, Term>(inst.u,
                anonUpdate);
        final InfFlowLoopInvariantTacletBuilder ifInvariantBuilder = new InfFlowLoopInvariantTacletBuilder(
                services);
        ifInvariantBuilder.setInvariant(spec);
        ifInvariantBuilder.setExecutionContext(inst.innermostExecutionContext);
        ifInvariantBuilder.setContextUpdate(/* inst.u */);
        ifInvariantBuilder.setProofObligationVars(instantiationVars);
        ifInvariantBuilder.setGuard(guardTerm);

        final Term loopInvApplPredTerm = ifInvariantBuilder
                .buildContractApplPredTerm();
        final Taclet informationFlowInvariantApp = ifInvariantBuilder
                .buildTaclet();

        // return information flow data
        InfFlowData infFlowData = new InfFlowData(instantiationVars, guardAtPre,
                guardAtPost, guardJb, guardTerm, localOutTerms, localOutsAtPre,
                localOutsAtPost, updates, loopInvApplPredTerm,
                informationFlowInvariantApp);
        return infFlowData;
    }

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private WhileInvariantRule() {
    }

    private static Term buildAtPostVar(Term varTerm, String suffix,
            Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable) varTerm.op())
                .getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = new String("_" + suffix);
        }
        final String name = tb.newName(varTerm.toString() + "_After" + suffix);
        final LocationVariable varAtPostVar = new LocationVariable(
                new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        final Term varAtPost = tb.var(varAtPostVar);
        return varAtPost;
    }

    private static Term buildBeforeVar(Term varTerm, Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable) varTerm.op())
                .getKeYJavaType();
        final String name = tb.newName(varTerm.toString() + "_Before");
        final LocationVariable varAtPreVar = new LocationVariable(
                new ProgramElementName(name), resultType);
        register(varAtPreVar, services);
        final Term varAtPre = tb.var(varAtPreVar);
        return varAtPre;
    }

    private static Term buildAfterVar(Term varTerm, Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable) varTerm.op())
                .getKeYJavaType();
        final String name = tb.newName(varTerm.toString() + "_After");
        final LocationVariable varAtPostVar = new LocationVariable(
                new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        final Term varAtPost = tb.var(varAtPostVar);
        return varAtPost;
    }

    private static ImmutableList<Term> buildLocalOutsAtPre(
            ImmutableList<Term> varTerms, Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<Term> localOuts = ImmutableSLList.<Term> nil();
        for (final Term varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable) varTerm.op())
                    .getKeYJavaType();

            final String name = tb.newName(varTerm.toString() + "_Before");
            final LocationVariable varAtPostVar = new LocationVariable(
                    new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final Term varAtPost = tb.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    private static ImmutableList<Term> buildLocalOutsAtPost(
            ImmutableList<Term> varTerms, Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<Term> localOuts = ImmutableSLList.<Term> nil();
        for (final Term varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable) varTerm.op())
                    .getKeYJavaType();

            final String name = tb.newName(varTerm.toString() + "_After");
            final LocationVariable varAtPostVar = new LocationVariable(
                    new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final Term varAtPost = tb.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    static void register(ProgramVariable pv, Services services) {
        final Namespace progVarNames = services.getNamespaces()
                .programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    private static void setUpInfFlowPartOfUseGoal(final InfFlowData infData,
            final Term baseHeap, Goal goal, Services services) {
        assert infData != null;
        final TermBuilder tb = services.getTermBuilder();
        final ProofObligationVars symbExecVars = infData.symbExecVars;
        final Term heapAtPreEq = tb.equals(symbExecVars.pre.heap, baseHeap);
        final Term heapAtPostEq = tb.equals(symbExecVars.post.heap, baseHeap);
        Term beforeAssumptions = tb.and(heapAtPreEq, tb.box(infData.guardJb,
                tb.equals(infData.guardAtPre, infData.guardTerm)));
        Iterator<Term> outsAtPre = infData.localOutsAtPre.iterator();
        for (Term locOut : infData.localOuts) {
            beforeAssumptions = tb.and(beforeAssumptions,
                    tb.equals(outsAtPre.next(), locOut));
        }

        Term selfAtPostAssumption =
                // if the method is not static and if it is no constructor
                (symbExecVars.pre.self != null
                        && symbExecVars.post.self != null) ?
                // then the self-variable does not change
                                tb.equals(symbExecVars.post.self,
                                        symbExecVars.pre.self)
                                :
                                // else there is nothing to say about self
                                tb.tt();
        Term afterAssumptions = tb.and(heapAtPostEq,
                tb.box(infData.guardJb,
                        tb.equals(infData.guardAtPost, infData.guardTerm)),
                selfAtPostAssumption);
        final Iterator<Term> outsAtPost = infData.localOutsAtPost.iterator();
        for (final Term locOut : infData.localOuts) {
            afterAssumptions = tb.and(afterAssumptions,
                    tb.equals(outsAtPost.next(), locOut));
        }

        final Term infFlowAssumptions = tb.apply(infData.updates.first,
                tb.and(beforeAssumptions, tb.apply(infData.updates.second,
                        tb.and(afterAssumptions, infData.applPredTerm))));

        goal.addFormula(new SequentFormula(infFlowAssumptions), true, false);
        goal.addTaclet(infData.infFlowApp,
                SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        final InfFlowProof proof = (InfFlowProof) goal.proof();
        proof.addIFSymbol(infData.applPredTerm);
        proof.addIFSymbol(infData.infFlowApp);
        proof.addGoalTemplates(infData.infFlowApp);
    }

    private static InfFlowData setUpInfFlowValidityGoal(Goal infFlowGoal,
            LoopInvariantBuiltInRuleApp ruleApp, final Instantiation inst,
            final JavaBlock guardJb,
            final ImmutableSet<ProgramVariable> localIns,
            final ImmutableSet<ProgramVariable> localOuts,
            final ImmutableList<AnonUpdateData> anonUpdateDatas,
            final Term anonUpdate, Services services)
            throws RuleAbortException {
        assert anonUpdateDatas.size() == 1 : "information flow "
                + "extension is at the " + "moment not compatible "
                + "with the non-base-heap " + "setting";
        final AnonUpdateData anonUpdateData = anonUpdateDatas.head();
        final TermBuilder tb = services.getTermBuilder();

        // reset validiy branch
        infFlowGoal.setBranchLabel("Information Flow Validity");

        // clear goal
        infFlowGoal.node().setSequent(Sequent.EMPTY_SEQUENT);
        infFlowGoal.clearAndDetachRuleAppIndex();

        // prepare data
        LoopSpecification inv = inst.inv;
        final Term guard = ruleApp.getGuard();
        InfFlowData infFlowData = prepareSetUpOfInfFlowValidityGoal(
                anonUpdateData, guard, inst, inv, services, ruleApp, localIns,
                localOuts, anonUpdate, guardJb);

        // generate information flow proof obligation variables
        final IFProofObligationVars ifVars = new IFProofObligationVars(
                infFlowData.symbExecVars, services);
        ruleApp.setInformationFlowProofObligationVars(ifVars);

        // set execution context
        ruleApp.setExecutionContext(inst.innermostExecutionContext);

        // create proof obligation
        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(inv,
                ifVars.c1, ifVars.c2, inst.innermostExecutionContext, guard,
                services);
        final Term selfComposedExec = f.create(
                InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
        final Term post = f.create(
                InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);

        final Term finalTerm = tb.imp(tb.label(selfComposedExec,
                ParameterlessTermLabel.SELF_COMPOSITION_LABEL), post);
        ((InfFlowProof) infFlowGoal.proof())
                .addLabeledIFSymbol(selfComposedExec);
        infFlowGoal.addFormula(new SequentFormula(finalTerm), false, true);

        return infFlowData;
    }

    // -------------------------------------------------------------------------
    // helper methods for apply()
    // -------------------------------------------------------------------------

    private Term bodyTerm(TermLabelState termLabelState, Services services,
            RuleApp ruleApp, final Sequent applicationSequent,
            Instantiation inst, final Term invTerm, Term frameCondition,
            final Term variantPO, Goal bodyGoal, final JavaBlock guardJb,
            final Term guardTrueTerm) {
        final WhileInvariantTransformer wir = new WhileInvariantTransformer();
        final TermBuilder tb = services.getTermBuilder();
        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS
                .replace(null, null, inst.innermostExecutionContext, null,
                        services);
        for (SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
            assert sv instanceof ProgramSV;
            svInst = svInst.addInteresting(sv,
                    (Name) new ProgramElementName(sv.name().toString()),
                    services);
        }
        Term fullInvariant = tb.and(invTerm, frameCondition, variantPO);
        fullInvariant = TermLabelManager.refactorTerm(termLabelState, services,
                null, fullInvariant, this, bodyGoal, FULL_INVARIANT_TERM_HINT,
                null);
        Term bodyTerm = wir.transform(termLabelState, this, ruleApp, bodyGoal,
                applicationSequent, ruleApp.posInOccurrence(), inst.progPost,
                fullInvariant, svInst, services);
        final Term guardTrueBody = tb.imp(tb.box(guardJb, guardTrueTerm),
                bodyTerm);
        return guardTrueBody;
    }

    private SequentFormula initFormula(TermLabelState termLabelState,
            Instantiation inst, final Term invTerm, Term reachableState,
            Services services, Goal initGoal) {
        final TermBuilder tb = services.getTermBuilder();
        Term sfTerm = tb.apply(inst.u, tb.and(invTerm, reachableState), null);
        sfTerm = TermLabelManager.refactorTerm(termLabelState, services, null,
                sfTerm, this, initGoal, INITIAL_INVARIANT_ONLY_HINT, null);
        return new SequentFormula(sfTerm);
    }

    private Term useCaseFormula(TermLabelState termLabelState,
            Services services, RuleApp ruleApp, Instantiation inst,
            Goal useGoal, final JavaBlock guardJb, final Term guardFalseTerm) {
        final TermBuilder tb = services.getTermBuilder();
        JavaBlock useJavaBlock = JavaTools
                .removeActiveStatement(inst.progPost.javaBlock(), services);
        final ImmutableArray<TermLabel> instantiateLabels = TermLabelManager
                .instantiateLabels(termLabelState, services,
                        ruleApp.posInOccurrence(), this, ruleApp, useGoal,
                        "UseModality", null, inst.progPost.op(),
                        new ImmutableArray<Term>(inst.progPost.sub(0)), null,
                        useJavaBlock, inst.progPost.getLabels());
        Term restPsi = tb.prog((Modality) inst.progPost.op(), useJavaBlock,
                inst.progPost.sub(0), instantiateLabels);
        Term guardFalseRestPsi = tb.box(guardJb,
                tb.imp(guardFalseTerm, restPsi));
        return guardFalseRestPsi;
    }

    private Triple<JavaBlock, Term, Term> prepareGuard(final Instantiation inst,
            final KeYJavaType booleanKJT,
            LoopInvariantBuiltInRuleApp loopRuleApp,
            final TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final ProgramElementName guardVarName = new ProgramElementName(
                tb.newName("b"));
        final LocationVariable guardVar = new LocationVariable(guardVarName,
                booleanKJT);
        services.getNamespaces().programVariables().addSafely(guardVar);
        loopRuleApp.setGuard(tb.var(guardVar));
        final VariableSpecification guardVarSpec = new VariableSpecification(
                guardVar, inst.loop.getGuardExpression(), booleanKJT);
        final LocalVariableDeclaration guardVarDecl = new LocalVariableDeclaration(
                new TypeRef(booleanKJT), guardVarSpec);
        final Statement guardVarMethodFrame = inst.innermostExecutionContext == null
                ? guardVarDecl
                : new MethodFrame(null, inst.innermostExecutionContext,
                        new StatementBlock(guardVarDecl));
        final JavaBlock guardJb = JavaBlock
                .createJavaBlock(new StatementBlock(guardVarMethodFrame));
        final Term guardTrueTerm = tb.equals(tb.var(guardVar), tb.TRUE());
        final Term guardFalseTerm = tb.equals(tb.var(guardVar), tb.FALSE());
        return new Triple<JavaBlock, Term, Term>(guardJb, guardTrueTerm,
                guardFalseTerm);
    }

    private void prepareInvInitiallyValidBranch(TermLabelState termLabelState,
            Services services, RuleApp ruleApp, Instantiation inst,
            final Term invTerm, Term reachableState, Goal initGoal) {
        initGoal.setBranchLabel("Invariant Initially Valid");
        initGoal.changeFormula(initFormula(termLabelState, inst, invTerm,
                reachableState, services, initGoal), ruleApp.posInOccurrence());
        TermLabelManager.refactorGoal(termLabelState, services,
                ruleApp.posInOccurrence(), this, initGoal, null, null);
    }

    private void prepareBodyPreservesBranch(TermLabelState termLabelState,
            Services services, RuleApp ruleApp,
            final Sequent applicationSequent, Instantiation inst,
            final Term invTerm, Term wellFormedAnon, Term frameCondition,
            final Term variantPO, Goal bodyGoal, final JavaBlock guardJb,
            final Term guardTrueTerm, final Term[] uBeforeLoopDefAnonVariant,
            final Term uAnonInv) {
        final TermBuilder tb = services.getTermBuilder();
        bodyGoal.setBranchLabel(BODY_PRESERVES_INVARIANT_LABEL);
        bodyGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);

        bodyGoal.addFormula(new SequentFormula(uAnonInv), true, false);

        Term guardTrueBody = bodyTerm(termLabelState, services, ruleApp,
                applicationSequent, inst, invTerm, frameCondition, variantPO,
                bodyGoal, guardJb, guardTrueTerm);

        bodyGoal.changeFormula(new SequentFormula(
                tb.applySequential(uBeforeLoopDefAnonVariant, guardTrueBody)),
                ruleApp.posInOccurrence());
    }

    private void prepareUseCaseBranch(TermLabelState termLabelState,
            Services services, RuleApp ruleApp, Instantiation inst,
            Term wellFormedAnon, Goal useGoal, final JavaBlock guardJb,
            final Term guardFalseTerm, final Term[] uAnon,
            final Term uAnonInv) {
        useGoal.setBranchLabel("Use Case");
        useGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
        useGoal.addFormula(new SequentFormula(uAnonInv), true, false);
        final TermBuilder tb = services.getTermBuilder();

        Term guardFalseRestPsi = useCaseFormula(termLabelState, services,
                ruleApp, inst, useGoal, guardJb, guardFalseTerm);
        useGoal.changeFormula(
                new SequentFormula(
                        tb.applySequential(uAnon, guardFalseRestPsi)),
                ruleApp.posInOccurrence());
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    static Pair<Term, Term> applyUpdates(Term focusTerm,
            TermServices services) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm),
                    UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<Term, Term>(services.getTermBuilder().skip(),
                    focusTerm);
        }
    }

    private void setupWdGoal(final Goal goal, final LoopSpecification inv,
            final Term update, final Term selfTerm, final LocationVariable heap,
            final Term anonHeap, final ImmutableSet<ProgramVariable> localIns,
            PosInOccurrence pio, Services services) {
        if (goal == null) {
            return;
        }
        goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
        final LoopWellDefinedness lwd = new LoopWellDefinedness(inv, localIns,
                services);
        final ProgramVariable self;
        if (selfTerm != null && selfTerm.op() instanceof ProgramVariable) {
            self = (ProgramVariable) selfTerm.op();
        } else {
            self = null;
        }
        services.getSpecificationRepository().addWdStatement(lwd);
        final SequentFormula wdInv = lwd.generateSequent(self, heap, anonHeap,
                localIns, update, services);
        goal.changeFormula(wdInv, pio);
    }

    @Override
    public Name name() {
        return NAME;
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class InfFlowData {
        public final ProofObligationVars symbExecVars;
        public final Term guardAtPre;
        public final Term guardAtPost;
        public final JavaBlock guardJb;
        public final Term guardTerm;
        public final ImmutableList<Term> localOuts;
        public final ImmutableList<Term> localOutsAtPre;
        public final ImmutableList<Term> localOutsAtPost;
        public final Pair<Term, Term> updates;
        public final Term applPredTerm;
        public final Taclet infFlowApp;

        private InfFlowData(ProofObligationVars symbExecVars, Term guardAtPre,
                Term guardAtPost, JavaBlock guardJb, Term guardTerm,
                ImmutableList<Term> localOuts,
                ImmutableList<Term> localOutsAtPre,
                ImmutableList<Term> localOutsAtPost, Pair<Term, Term> updates,
                Term applPredTerm, Taclet infFlowApp) {
            this.symbExecVars = symbExecVars;
            this.guardAtPre = guardAtPre;
            this.guardAtPost = guardAtPost;
            this.guardJb = guardJb;
            this.guardTerm = guardTerm;
            this.localOuts = localOuts;
            this.localOutsAtPre = localOutsAtPre;
            this.localOutsAtPost = localOutsAtPost;
            this.updates = updates;
            this.infFlowApp = infFlowApp;
            this.applPredTerm = applPredTerm;

            assert symbExecVars != null;
            assert guardAtPre != null;
            assert guardAtPost != null;
            assert guardJb != null;
            assert guardTerm != null;
            assert localOuts != null;
            assert localOutsAtPre != null;
            assert localOutsAtPost != null;
            assert updates != null;
            assert applPredTerm != null;
            assert infFlowApp != null;
        }
    }
}
