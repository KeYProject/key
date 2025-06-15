/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowLoopInvariantTacletBuilder;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvariantTransformer;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.LoopWellDefinedness;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NonNull;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

public final class WhileInvariantRule implements BuiltInRule {
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



    private static InfFlowData prepareSetUpOfInfFlowValidityGoal(final Goal infFlowGoal,
            final AnonUpdateData anonUpdateData, final JTerm guardTerm, final Instantiation inst,
            LoopSpecification spec, Services services, LoopInvariantBuiltInRuleApp ruleApp,
            final ImmutableSet<LocationVariable> localIns,
            final ImmutableSet<LocationVariable> localOuts, final JTerm anonUpdate,
            final JavaBlock guardJb) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();
        final JTerm baseHeap = anonUpdateData.loopHeapAtPre;
        final JTerm selfTerm = inst.selfTerm;

        services.getSpecificationRepository().addLoopInvariant(spec);
        ruleApp.setLoopInvariant(spec);
        instantiate(ruleApp, services);

        // create heap_Before_LOOP
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Name heapAtPreName = new Name(tb.newName(baseHeap + "_Before_LOOP"));
        final Function heapAtPreFunc =
            new JFunction(heapAtPreName, heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(heapAtPreFunc);
        final JTerm heapAtPre = tb.func(heapAtPreFunc);

        final JTerm heapAtPost = anonUpdateData.loopHeap;
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
        final Pair<JTerm, JTerm> updates = new Pair<>(inst.u, anonUpdate);
        final InfFlowLoopInvariantTacletBuilder ifInvariantBuilder =
            new InfFlowLoopInvariantTacletBuilder(services);
        ifInvariantBuilder.setInvariant(spec);
        ifInvariantBuilder.setExecutionContext(inst.innermostExecutionContext);
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


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private WhileInvariantRule() {
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static Instantiation instantiate(final LoopInvariantBuiltInRuleApp app,
            Services services) throws RuleAbortException {
        final JTerm focusTerm = (JTerm) app.posInOccurrence().subTerm();

        // leading update?
        final Pair<JTerm, JTerm> update = applyUpdates(focusTerm, services);
        final JTerm u = update.first;
        final JTerm progPost = update.second;

        // focus (below update) must be modality term
        if (!checkFocus(progPost)) {
            return null;
        }

        // active statement must be while loop
        final While loop = app.getLoopStatement();

        // try to get invariant from JML specification
        LoopSpecification spec = app.getSpec();
        if (spec == null) {
            throw new RuleAbortException("no invariant found");
        }

        // collect self, execution context
        final MethodFrame innermostMethodFrame =
            JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
        if (innermostMethodFrame != null) {
            spec = spec.setTarget(innermostMethodFrame.getProgramMethod());
        }

        final JTerm selfTerm = innermostMethodFrame == null ? null
                : MiscTools.getSelfTerm(innermostMethodFrame, services);

        final ExecutionContext innermostExecutionContext = innermostMethodFrame == null ? null
                : (ExecutionContext) innermostMethodFrame.getExecutionContext();
        services.getSpecificationRepository().addLoopInvariant(spec);

        // cache and return result
        return new Instantiation(u, progPost, loop, spec, selfTerm, innermostExecutionContext);
    }

    private static JTerm createLocalAnonUpdate(ImmutableSet<LocationVariable> localOuts,
            Services services) {
        JTerm anonUpdate = null;
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable pv : localOuts) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final Function anonFunc = new JFunction(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final JTerm elemUpd = tb.elementary(pv, tb.func(anonFunc));
            if (anonUpdate == null) {
                anonUpdate = elemUpd;
            } else {
                anonUpdate = tb.parallel(anonUpdate, elemUpd);
            }
        }
        return anonUpdate;
    }

    /**
     * @return (assumption, anon update, anon heap)
     */
    private static AnonUpdateData createAnonUpdate(LocationVariable heap, JTerm modifiable,
            LoopSpecification inv, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final Name loopHeapName = new Name(tb.newName(heap + "_After_LOOP"));
        final Function loopHeapFunc =
            new JFunction(loopHeapName, heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(loopHeapFunc);

        final JTerm loopHeap = tb.func(loopHeapFunc);
        final Name anonHeapName = new Name(tb.newName("anon_" + heap + "_LOOP"));
        final Function anonHeapFunc = new JFunction(anonHeapName, heap.sort());
        services.getNamespaces().functions().addSafely(anonHeapFunc);
        final JTerm anonHeapTerm =
            tb.label(tb.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);

        // check for strictly pure loops
        final JTerm anonUpdate;
        if (tb.strictlyNothing().equalsModProperty(modifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
            anonUpdate = tb.skip();
        } else {
            anonUpdate = tb.anonUpd(heap, modifiable, anonHeapTerm);
        }

        return new AnonUpdateData(anonUpdate, loopHeap, tb.getBaseHeap(), anonHeapTerm);
    }

    private static boolean checkFocus(final JTerm progPost) {
        // focus (below update) must be modality term
        return progPost.op() instanceof JModality;
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
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    private static void setUpInfFlowPartOfUseGoal(final InfFlowData infData, final JTerm baseHeap,
            Goal goal, Services services) {
        assert infData != null;
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

    private static InfFlowData setUpInfFlowValidityGoal(Goal infFlowGoal,
            LoopInvariantBuiltInRuleApp ruleApp, final Instantiation inst, final JavaBlock guardJb,
            final ImmutableSet<LocationVariable> localIns,
            final ImmutableSet<LocationVariable> localOuts,
            final ImmutableList<AnonUpdateData> anonUpdateDatas, final JTerm anonUpdate,
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
        LoopSpecification inv = inst.inv;
        final JTerm guard = ruleApp.getGuard();
        InfFlowData infFlowData = prepareSetUpOfInfFlowValidityGoal(infFlowGoal, anonUpdateData,
            guard, inst, inv, services, ruleApp, localIns, localOuts, anonUpdate, guardJb);

        // generate information flow proof obligation variables
        final IFProofObligationVars ifVars =
            new IFProofObligationVars(infFlowData.symbExecVars, services);
        ruleApp.setInformationFlowProofObligationVars(ifVars);

        // set execution context
        ruleApp.setExecutionContext(inst.innermostExecutionContext);

        // create proof obligation
        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(inv, ifVars.c1, ifVars.c2,
            inst.innermostExecutionContext, guard, services);
        final JTerm selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
        final JTerm post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);

        final JTerm finalTerm =
            tb.imp(tb.label(selfComposedExec, ParameterlessTermLabel.SELF_COMPOSITION_LABEL), post);
        ((InfFlowProof) infFlowGoal.proof()).addLabeledIFSymbol(selfComposedExec);
        infFlowGoal.addFormula(new SequentFormula(finalTerm), false, true);

        return infFlowData;
    }

    // -------------------------------------------------------------------------
    // helper methods for apply()
    // -------------------------------------------------------------------------

    private JTerm conjunctInv(Services services, Instantiation inst,
            final Map<LocationVariable, JTerm> atPres, final List<LocationVariable> heapContext) {
        JTerm invTerm = services.getTermBuilder().tt();
        for (LocationVariable heap : heapContext) {
            final JTerm i = inst.inv.getInvariant(heap, inst.selfTerm, atPres, services);
            if (i == null) {
                continue;
            }
            if (invTerm == null) {
                invTerm = i;
            } else {
                invTerm = services.getTermBuilder().and(invTerm, i);
            }
        }
        return invTerm;
    }

    private JTerm conjunctFreeInv(Services services, Instantiation inst,
            final Map<LocationVariable, JTerm> atPres, final List<LocationVariable> heapContext) {
        JTerm freeInvTerm = services.getTermBuilder().tt();
        for (LocationVariable heap : heapContext) {
            final JTerm i = inst.inv.getFreeInvariant(heap, inst.selfTerm, atPres, services);
            if (i == null) {
                continue;
            }
            if (freeInvTerm == null) {
                freeInvTerm = i;
            } else {
                freeInvTerm = services.getTermBuilder().and(freeInvTerm, i);
            }
        }
        return freeInvTerm;
    }

    private Pair<JTerm, JTerm> prepareVariant(Instantiation inst, JTerm variant,
            TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final ProgramElementName variantName = new ProgramElementName(tb.newName("variant"));
        final LocationVariable variantPV = new LocationVariable(variantName, JavaDLTheory.ANY);
        services.getNamespaces().programVariables().addSafely(variantPV);

        Modality modality = ((Modality) inst.progPost.op());
        final boolean dia = modality.<JModality.JavaModalityKind>kind().terminationSensitive();
        final JTerm variantUpdate = dia ? tb.elementary(variantPV, variant) : tb.skip();
        final JTerm variantPO = dia ? tb.prec(variant, tb.var(variantPV)) : tb.tt();
        return new Pair<>(variantUpdate, variantPO);
    }


    private JTerm bodyTerm(TermLabelState termLabelState, Services services,
            RuleApp ruleApp,
            final Sequent applicationSequent, Instantiation inst, final JTerm invTerm,
            JTerm frameCondition, final JTerm variantPO, Goal bodyGoal, final JavaBlock guardJb,
            final JTerm guardTrueTerm) {
        final WhileInvariantTransformer wir = new WhileInvariantTransformer();
        final TermBuilder tb = services.getTermBuilder();
        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS.replace(null, null,
            inst.innermostExecutionContext, null, services);
        for (SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
            assert sv instanceof ProgramSV;
            svInst = svInst.addInteresting(sv, (Name) new ProgramElementName(sv.name().toString()),
                services);
        }
        JTerm fullInvariant = tb.and(invTerm, frameCondition, variantPO);
        fullInvariant = TermLabelManager.refactorTerm(termLabelState, services, null, fullInvariant,
            this, bodyGoal, FULL_INVARIANT_TERM_HINT, null);
        JTerm bodyTerm = wir.transform(termLabelState, this, ruleApp, bodyGoal, applicationSequent,
            ruleApp.posInOccurrence(), inst.progPost, fullInvariant, svInst, services);
        return tb.imp(tb.box(guardJb, guardTrueTerm), bodyTerm);
    }


    private SequentFormula initFormula(TermLabelState termLabelState,
            Instantiation inst,
            final JTerm invTerm, JTerm reachableState, Services services, Goal initGoal) {
        final TermBuilder tb = services.getTermBuilder();
        JTerm sfTerm = tb.apply(inst.u, tb.and(invTerm, reachableState), null);
        sfTerm = TermLabelManager.refactorTerm(termLabelState, services, null, sfTerm, this,
            initGoal, INITIAL_INVARIANT_ONLY_HINT, null);
        return new SequentFormula(sfTerm);
    }

    private JTerm useCaseFormula(TermLabelState termLabelState, Services services,
            RuleApp ruleApp,
            Instantiation inst, Goal useGoal, final JavaBlock guardJb, final JTerm guardFalseTerm) {
        final TermBuilder tb = services.getTermBuilder();
        JavaBlock useJavaBlock =
            JavaTools.removeActiveStatement(inst.progPost.javaBlock(), services);
        var modality = (Modality) inst.progPost.op();
        final ImmutableArray<TermLabel> instantiateLabels = TermLabelManager.instantiateLabels(
            termLabelState, services, ruleApp.posInOccurrence(), this, ruleApp, useGoal,
            "UseModality", null,
            tb.tf().createTerm(JModality.getModality(modality.kind(), useJavaBlock),
                new ImmutableArray<>(inst.progPost.sub(0)),
                null, inst.progPost.getLabels()));
        JTerm restPsi =
            tb.prog(modality.kind(), useJavaBlock, inst.progPost.sub(0),
                instantiateLabels);
        return tb.box(guardJb, tb.imp(guardFalseTerm, restPsi));
    }

    private Guard prepareGuard(final Instantiation inst,
            final KeYJavaType booleanKJT, LoopInvariantBuiltInRuleApp loopRuleApp,
            final TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final ProgramElementName guardVarName = new ProgramElementName(tb.newName("b"));
        final LocationVariable guardVar = new LocationVariable(guardVarName, booleanKJT);
        services.getNamespaces().programVariables().addSafely(guardVar);
        loopRuleApp.setGuard(tb.var(guardVar));
        final VariableSpecification guardVarSpec =
            new VariableSpecification(guardVar, inst.loop.getGuardExpression(), booleanKJT);
        final LocalVariableDeclaration guardVarDecl =
            new LocalVariableDeclaration(new TypeRef(booleanKJT), guardVarSpec);
        final Statement guardVarMethodFrame = inst.innermostExecutionContext == null ? guardVarDecl
                : new MethodFrame(null, inst.innermostExecutionContext,
                    new StatementBlock(guardVarDecl));
        final JavaBlock guardJb =
            JavaBlock.createJavaBlock(new StatementBlock(guardVarMethodFrame));
        final JTerm guardTrueTerm = tb.equals(tb.var(guardVar), tb.TRUE());
        final JTerm guardFalseTerm = tb.equals(tb.var(guardVar), tb.FALSE());
        return new Guard(guardJb, guardTrueTerm, guardFalseTerm);
    }

    /**
     * Represents a {@code javaBlock} which is executed if the {@code trueTerm} is true.
     *
     * @param javaBlock a block of java code
     * @param trueTerm a boolean term
     * @param falseTerm the negation (at least semantically) of {@code trueTerm}
     */
    private record Guard(JavaBlock javaBlock, JTerm trueTerm, JTerm falseTerm) {
    }

    private void prepareInvInitiallyValidBranch(TermLabelState termLabelState, Services services,
            RuleApp ruleApp, Instantiation inst, final JTerm invTerm,
            JTerm reachableState,
            Goal initGoal) {
        initGoal.setBranchLabel("Invariant Initially Valid");
        initGoal.changeFormula(
            initFormula(termLabelState, inst, invTerm, reachableState, services, initGoal),
            ruleApp.posInOccurrence());
        TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(), this,
            initGoal, null, null);
    }


    private void prepareBodyPreservesBranch(TermLabelState termLabelState, Services services,
            RuleApp ruleApp, final Sequent applicationSequent,
            Instantiation inst,
            final JTerm invTerm, JTerm wellFormedAnon, JTerm frameCondition, final JTerm variantPO,
            Goal bodyGoal, final JavaBlock guardJb, final JTerm guardTrueTerm,
            final JTerm[] uBeforeLoopDefAnonVariant, final JTerm uAnonInv) {
        final TermBuilder tb = services.getTermBuilder();
        bodyGoal.setBranchLabel(BODY_PRESERVES_INVARIANT_LABEL);
        bodyGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);

        bodyGoal.addFormula(new SequentFormula(uAnonInv), true, false);

        JTerm guardTrueBody = bodyTerm(termLabelState, services, ruleApp, applicationSequent, inst,
            invTerm, frameCondition, variantPO, bodyGoal, guardJb, guardTrueTerm);

        bodyGoal.changeFormula(
            new SequentFormula(tb.applySequential(uBeforeLoopDefAnonVariant, guardTrueBody)),
            ruleApp.posInOccurrence());
    }


    private void prepareUseCaseBranch(TermLabelState termLabelState, Services services,
            RuleApp ruleApp, Instantiation inst, JTerm wellFormedAnon,
            Goal useGoal,
            final JavaBlock guardJb, final JTerm guardFalseTerm, final JTerm[] uAnon,
            final JTerm uAnonInv) {
        useGoal.setBranchLabel("Use Case");
        useGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
        useGoal.addFormula(new SequentFormula(uAnonInv), true, false);
        final TermBuilder tb = services.getTermBuilder();

        JTerm guardFalseRestPsi = useCaseFormula(termLabelState, services, ruleApp, inst, useGoal,
            guardJb, guardFalseTerm);
        useGoal.changeFormula(new SequentFormula(tb.applySequential(uAnon, guardFalseRestPsi)),
            ruleApp.posInOccurrence());
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return checkApplicability(goal, pio);
    }


    // focus must be top level succedent
    static boolean checkApplicability(Goal g, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }
        Pair<JTerm, JTerm> up = applyUpdates((JTerm) pio.subTerm(), g.proof().getServices());
        final JTerm progPost = up.second;
        if (!checkFocus(progPost)) {
            return false;
        }
        // active statement must be while loop
        final SourceElement activeStatement = JavaTools.getActiveStatement(progPost.javaBlock());
        return activeStatement instanceof While;
    }

    static Pair<JTerm, JTerm> applyUpdates(JTerm focusTerm, TermServices services) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<>(UpdateApplication.getUpdate(focusTerm),
                UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<>(services.getTermBuilder().skip(), focusTerm);
        }
    }

    private void setupWdGoal(final Goal goal, final LoopSpecification inv, final JTerm update,
            final JTerm selfTerm, final LocationVariable heap, final JTerm anonHeap,
            final JTerm localAnonUpdate, final ImmutableSet<LocationVariable> localIns,
            PosInOccurrence pio, Services services) {
        if (goal == null) {
            return;
        }
        goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
        final LoopWellDefinedness lwd = new LoopWellDefinedness(inv, localIns, services);
        final LocationVariable self;
        if (selfTerm != null && selfTerm.op() instanceof LocationVariable) {
            self = (LocationVariable) selfTerm.op();
        } else {
            self = null;
        }
        services.getSpecificationRepository().addWdStatement(lwd);
        final SequentFormula wdInv =
            lwd.generateSequent(self, heap, anonHeap, localIns, update, localAnonUpdate, services);
        goal.changeFormula(wdInv, pio);
    }


    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, final RuleApp ruleApp)
            throws RuleAbortException {
        final TermLabelState termLabelState = new TermLabelState();
        assert ruleApp instanceof LoopInvariantBuiltInRuleApp;
        LoopInvariantBuiltInRuleApp loopRuleApp = (LoopInvariantBuiltInRuleApp) ruleApp;
        final Sequent applicationSequent = goal.sequent();
        final var services = goal.getOverlayServices();
        final KeYJavaType booleanKJT = services.getTypeConverter().getBooleanType();
        final TermBuilder tb = services.getTermBuilder();

        // get instantiation
        final Instantiation inst = instantiate(loopRuleApp, services);

        final Map<LocationVariable, JTerm> atPres = inst.inv.getInternalAtPres();
        final List<LocationVariable> heapContext = ((IBuiltInRuleApp) ruleApp).getHeapContext();

        final JTerm invTerm = conjunctInv(services, inst, atPres, heapContext);
        final JTerm invFreeTerm = conjunctFreeInv(services, inst, atPres, heapContext);

        final Map<LocationVariable, JTerm> modifiables = new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> freeModifiables = new LinkedHashMap<>();
        for (LocationVariable heap : heapContext) {
            modifiables.put(heap, inst.inv.getModifiable(heap, inst.selfTerm, atPres, services));
            freeModifiables.put(heap,
                inst.inv.getFreeModifiable(heap, inst.selfTerm, atPres, services));
        }

        final JTerm variant = inst.inv.getVariant(inst.selfTerm, atPres, services);

        // collect input and output local variables,
        // prepare reachableIn and reachableOut
        final ImmutableSet<LocationVariable> localIns = MiscTools.getLocalIns(inst.loop, services);
        final ImmutableSet<LocationVariable> localOuts =
            MiscTools.getLocalOuts(inst.loop, services);
        JTerm reachableIn = tb.tt();
        for (var pv : localIns) {
            reachableIn = tb.and(reachableIn, tb.reachableValue(pv));
        }
        JTerm reachableOut = tb.tt();

        for (var pv : localOuts) {
            reachableOut = tb.and(reachableOut, tb.reachableValue(pv));
        }

        // prepare variant
        final Pair<JTerm, JTerm> variantPair = prepareVariant(inst, variant, services);
        final JTerm variantUpdate = variantPair.first;
        final JTerm variantPO = variantPair.second;

        // prepare guard
        final Guard guardStuff =
            prepareGuard(inst, booleanKJT, loopRuleApp, services);
        final JavaBlock guardJb = guardStuff.javaBlock;
        final JTerm guardTrueTerm = guardStuff.trueTerm;
        final JTerm guardFalseTerm = guardStuff.falseTerm;

        JTerm beforeLoopUpdate = null;

        final Map<LocationVariable, Map<JTerm, JTerm>> heapToBeforeLoop =
            new LinkedHashMap<>();

        for (LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<>());
            final LocationVariable lv =
                tb.locationVariable(heap + "Before_LOOP", heap.sort(), true);
            services.getNamespaces().programVariables().addSafely(lv);
            final JTerm u = tb.elementary(lv, tb.var(heap));
            if (beforeLoopUpdate == null) {
                beforeLoopUpdate = u;
            } else {
                beforeLoopUpdate = tb.parallel(beforeLoopUpdate, u);
            }
            heapToBeforeLoop.get(heap).put(tb.var(heap), tb.var(lv));
        }

        // This is needed because of the shallow access of \permission,
        // heap references that are deeper than top-level have to be replaced to, but with
        // heapBefore_....
        final LocationVariable permissionHeap =
            services.getTypeConverter().getHeapLDT().getPermissionHeap();
        if (permissionHeap != null && heapContext.contains(permissionHeap)) {
            final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
            final JTerm baseHeapVar = services.getTermBuilder().var(baseHeap);
            heapToBeforeLoop.get(permissionHeap).put(baseHeapVar,
                heapToBeforeLoop.get(baseHeap).get(baseHeapVar));
        }

        for (ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName = tb.newName(pv.name() + "Before_LOOP");
            final LocationVariable pvBeforeLoop =
                new LocationVariable(new ProgramElementName(pvBeforeLoopName), pv.getKeYJavaType());
            services.getNamespaces().programVariables().addSafely(pvBeforeLoop);
            beforeLoopUpdate =
                tb.parallel(beforeLoopUpdate, tb.elementary(pvBeforeLoop, tb.var(pv)));
            heapToBeforeLoop.get(services.getTypeConverter().getHeapLDT().getHeap()).put(tb.var(pv),
                tb.var(pvBeforeLoop));
        }

        // prepare anon update, frame condition, etc.
        JTerm anonUpdate = createLocalAnonUpdate(localOuts, services); // can still be null
        final JTerm localAnonUpdate = anonUpdate != null ? anonUpdate : tb.skip();
        // Term anonAssumption = null;
        JTerm wellFormedAnon = null;
        JTerm frameCondition = null;
        JTerm reachableState = null;
        JTerm anonHeap = null;
        ImmutableList<AnonUpdateData> anonUpdateDatas = ImmutableSLList.nil();
        for (LocationVariable heap : heapContext) {
            final AnonUpdateData tAnon =
                createAnonUpdate(heap, modifiables.get(heap), inst.inv, services);
            anonUpdateDatas = anonUpdateDatas.append(tAnon);
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
            if (anonHeap == null) {
                anonHeap = tAnon.anonHeap;
            }
            final JTerm modifiable = modifiables.get(heap);
            final JTerm freeModifiable = freeModifiables.get(heap);
            final JTerm strictlyNothing = tb.strictlyNothing();
            final JTerm currentFrame;
            if (strictlyNothing.equalsModProperty(
                modifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                if (strictlyNothing.equalsModProperty(
                    freeModifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    currentFrame = tb.frameStrictlyEmpty(tb.var(heap), heapToBeforeLoop.get(heap));
                } else {
                    currentFrame =
                        tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), freeModifiable);
                }
            } else {
                if (strictlyNothing.equalsModProperty(
                    freeModifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    currentFrame = tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), modifiable);
                } else {
                    currentFrame = tb.frame(
                        tb.var(heap), heapToBeforeLoop.get(heap),
                        tb.union(modifiable, freeModifiable));
                }
            }
            if (frameCondition == null) {
                frameCondition = currentFrame;
            } else {
                frameCondition = tb.and(frameCondition, currentFrame);
            }
            if (reachableState == null) {
                reachableState = tb.wellFormed(heap);
            } else {
                reachableState = tb.and(reachableState, tb.wellFormed(heap));
            }
        }

        // prepare common assumption
        final JTerm[] uAnon = { inst.u, anonUpdate };
        final JTerm[] uBeforeLoopDefAnonVariant =
            { inst.u, beforeLoopUpdate, anonUpdate, variantUpdate };
        final JTerm uAnonInv =
            tb.applySequential(uAnon, tb.and(tb.and(invTerm, reachableOut), invFreeTerm));

        final ImmutableList<Goal> result;
        Goal wdGoal;
        if (WellDefinednessCheck.isOn()) {
            // split goal into four branches
            result = goal.split(4);
            wdGoal = result.tail().tail().tail().head();
            wdGoal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
        } else {
            // split goal into three branches
            result = goal.split(3);
            wdGoal = null;
        }
        Goal initGoal = result.tail().tail().head();
        Goal bodyGoal = result.tail().head();
        Goal useGoal = result.head();

        // "Invariant Initially Valid":
        // \replacewith (==> inv );
        prepareInvInitiallyValidBranch(termLabelState, services, ruleApp, inst, invTerm,
            reachableState, initGoal);

        // "Body Preserves Invariant":
        // \replacewith (==> #atPreEqs(anon1)
        // -> #introNewAnonUpdate(#modifiable, #locDepFunc(anon1,
        // \[{.. while (#e) #s ...}\]post) & inv ->
        // (\[{ method-frame(#ex){#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
        // #whileInvRule(\[{.. while (#e) #s ...}\]post,
        // #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post)
        // & inv)),
        // anon1));
        prepareBodyPreservesBranch(termLabelState, services, ruleApp, applicationSequent, inst,
            invTerm, wellFormedAnon, frameCondition, variantPO, bodyGoal, guardJb, guardTrueTerm,
            uBeforeLoopDefAnonVariant, uAnonInv);

        if (InfFlowCheckInfo.isInfFlow(goal) && inst.inv.hasInfFlowSpec(services)) {
            // set up information flow validity goal
            InfFlowData infFlowData = setUpInfFlowValidityGoal(bodyGoal, loopRuleApp, inst, guardJb,
                localIns, localOuts, anonUpdateDatas, anonUpdate, services);

            // set up information flow part of useGoal:
            // add infFlowAssumptions, add term and taclet to post goal
            setUpInfFlowPartOfUseGoal(infFlowData, anonUpdateDatas.head().loopHeapAtPre, useGoal,
                services);
        }

        setupWdGoal(wdGoal, inst.inv, inst.u, inst.selfTerm, heapContext.get(0), anonHeap,
            localAnonUpdate, localIns, ruleApp.posInOccurrence(), services);

        // "Use Case":
        // \replacewith (==> #introNewAnonUpdate(#modifiable, inv ->
        // (\[{ method-frame(#ex){#typeof(#e) #v1 = #e;} }\]
        // (#v1=FALSE -> \[{.. ...}\]post)),anon2))
        prepareUseCaseBranch(termLabelState, services, ruleApp, inst, wellFormedAnon, useGoal,
            guardJb, guardFalseTerm, uAnon, uAnonInv);
        return result;
    }


    @Override
    public Name name() {
        return NAME;
    }


    @Override
    public String displayName() {
        return toString();
    }


    @Override
    public String toString() {
        return NAME.toString();
    }


    @Override
    public LoopInvariantBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new LoopInvariantBuiltInRuleApp(this, pos, services);
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class Instantiation {
        /** The update term. */
        public final JTerm u;
        /** The program's post condition. */
        public final JTerm progPost;
        /** The while loop. */
        public final While loop;
        /** The invariant's loop specification. */
        public final LoopSpecification inv;
        /** The term for the self variable. */
        public final JTerm selfTerm;
        /** The innermost execution context. */
        public final ExecutionContext innermostExecutionContext;

        public Instantiation(JTerm u, JTerm progPost, While loop, LoopSpecification inv,
                JTerm selfTerm, ExecutionContext innermostExecutionContext) {
            assert u != null;
            assert u.sort() == JavaDLTheory.UPDATE;
            assert progPost != null;
            assert progPost.sort() == JavaDLTheory.FORMULA;
            assert loop != null;
            assert inv != null;
            this.u = u;
            this.progPost = progPost;
            this.loop = loop;
            this.inv = inv;
            this.selfTerm = selfTerm;
            this.innermostExecutionContext = innermostExecutionContext;
        }
    }

    private static class AnonUpdateData {
        public final JTerm anonUpdate, anonHeap, loopHeap, loopHeapAtPre;

        public AnonUpdateData(JTerm anonUpdate, JTerm loopHeap, JTerm loopHeapAtPre,
                JTerm anonHeap) {
            this.anonUpdate = anonUpdate;
            this.loopHeap = loopHeap;
            this.loopHeapAtPre = loopHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }

    private record InfFlowData(ProofObligationVars symbExecVars, JTerm guardAtPre,
            JTerm guardAtPost,
            JavaBlock guardJb,
            JTerm guardTerm, ImmutableList<JTerm> localOuts, ImmutableList<JTerm> localOutsAtPre,
            ImmutableList<JTerm> localOutsAtPost, Pair<JTerm, JTerm> updates, JTerm applPredTerm,
            Taclet infFlowApp) {
        private InfFlowData(ProofObligationVars symbExecVars, JTerm guardAtPre, JTerm guardAtPost,
                JavaBlock guardJb, JTerm guardTerm, ImmutableList<JTerm> localOuts,
                ImmutableList<JTerm> localOutsAtPre, ImmutableList<JTerm> localOutsAtPost,
                Pair<JTerm, JTerm> updates, JTerm applPredTerm, Taclet infFlowApp) {
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

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }
}
