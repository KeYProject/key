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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvariantTransformer;
import de.uka.ilkd.key.rule.tacletbuilder.InfFlowLoopInvariantTacletBuilder;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopWellDefinedness;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

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

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;


    private static InfFlowData prepareSetUpOfInfFlowValidityGoal(final AnonUpdateData anonUpdateData,
                                                                 final Term guardTerm,
                                                                 final Instantiation inst,
                                                                 LoopInvariant inv,
                                                                 Services services,
                                                                 LoopInvariantBuiltInRuleApp ruleApp,
                                                                 final ImmutableSet<ProgramVariable> localIns,
                                                                 final ImmutableSet<ProgramVariable> localOuts,
                                                                 final Term anonUpdate,
                                                                 final JavaBlock guardJb)
            throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();
        final Term baseHeap = anonUpdateData.loopHeapAtPre;
        final Term selfTerm = inst.selfTerm;

        services.getSpecificationRepository().addLoopInvariant(inv);
        ruleApp.setLoopInvariant(inv);
        instantiate(ruleApp, services);

        // create heap_Before_LOOP
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Name heapAtPreName = new Name(tb.newName(baseHeap + "_Before_LOOP"));
        final Function heapAtPreFunc = new Function(heapAtPreName, heapLDT.targetSort(), true);
	services.getNamespaces().functions().addSafely(heapAtPreFunc);
        final Term heapAtPre = tb.func(heapAtPreFunc);

        final Term heapAtPost = anonUpdateData.loopHeap;
        final Term guardAtPre = buildBeforeVar(guardTerm, services);
        final Term guardAtPost = buildAfterVar(guardTerm, services);
        final Term selfAtPost = buildAtPostVar(selfTerm, "LOOP", services);
        // The set of local variables which are read in the loop body.
        final ImmutableList<Term> localInTerms = MiscTools.toTermList(localIns, tb);
        // The set of local variables which are written in the loop body.
        final ImmutableList<Term> localOutTerms = MiscTools.toTermList(localOuts, tb);
        // For every local variable which is written we need a pre and a post variable.
        final ImmutableList<Term> localOutsAtPre = buildLocalOutsAtPre(localOutTerms, services);
        final ImmutableList<Term> localOutsAtPost = buildLocalOutsAtPost(localOutTerms, services);
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
        final ImmutableList<Term> localInsWithoutOutDuplicates =
                MiscTools.filterOutDuplicates(localInTerms, localOutTerms);
        // The set of local pre variables is the union of the pre variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<Term> localVarsAtPre =
                localInsWithoutOutDuplicates.append(localOutsAtPre);
        // The set of local post variables is the union of the post variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<Term> localVarsAtPost =
                localInsWithoutOutDuplicates.append(localOutsAtPost);

        // generate proof obligation variables
        final StateVars instantiationPreVars =
                new StateVars(selfTerm, guardAtPre, localVarsAtPre, heapAtPre);
        final StateVars instantiationPostVars =
                new StateVars(selfAtPost, guardAtPost, localVarsAtPost, heapAtPost);
        final ProofObligationVars instantiationVars =
                new ProofObligationVars(instantiationPreVars,
                                        instantiationPostVars,
                                        services);

        // generate information flow invariant application predicate
        // and associated taclet
        final Pair<Term, Term> updates = new Pair<Term, Term> (inst.u, anonUpdate);
        final InfFlowLoopInvariantTacletBuilder ifInvariantBuilder =
                new InfFlowLoopInvariantTacletBuilder(services);
        ifInvariantBuilder.setInvariant(inv);
        ifInvariantBuilder.setExecutionContext(inst.innermostExecutionContext);
        ifInvariantBuilder.setContextUpdate(/*inst.u*/);
        ifInvariantBuilder.setProofObligationVars(instantiationVars);
        ifInvariantBuilder.setGuard(guardTerm);

        final Term loopInvApplPredTerm =
                ifInvariantBuilder.buildContractApplPredTerm();
        final Taclet informationFlowInvariantApp =
                ifInvariantBuilder.buildTaclet();

        // return information flow data
        InfFlowData infFlowData = new InfFlowData(instantiationVars, guardAtPre,
                                                  guardAtPost, guardJb,
                                                  guardTerm, localOutTerms,
                                                  localOutsAtPre, localOutsAtPost,
                                                  updates, loopInvApplPredTerm,
                                                  informationFlowInvariantApp);
        return infFlowData;
    }


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private WhileInvariantRule() {
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private static Instantiation instantiate(final LoopInvariantBuiltInRuleApp app,
                                             Services services) throws RuleAbortException {
        final Term focusTerm = app.posInOccurrence().subTerm();

        if (focusTerm == lastFocusTerm &&
                lastInstantiation.inv == services.getSpecificationRepository()
                .getLoopInvariant(lastInstantiation.loop)) {
            return lastInstantiation;
        }

	//leading update?
	final Pair<Term, Term> update = applyUpdates(focusTerm, services);
	final Term u        = update.first;
	final Term progPost = update.second;

	//focus (below update) must be modality term
        if (!checkFocus(progPost)) {
            return null;
        }

	//active statement must be while loop
	final While loop = app.getLoopStatement();

	// try to get invariant from JML specification
	LoopInvariant inv = app.getInvariant();
	if (inv == null) // may happen after reloading proof 
	    throw new RuleAbortException("no invariant found");

	//collect self, execution context
	final MethodFrame innermostMethodFrame =
	        JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
	inv = inv.setTarget(innermostMethodFrame.getProgramMethod());

	final Term selfTerm = innermostMethodFrame == null
	                      ? null
	                      : MiscTools.getSelfTerm(innermostMethodFrame, services);

	final ExecutionContext innermostExecutionContext =
	        innermostMethodFrame == null
	        ? null
	        : (ExecutionContext) innermostMethodFrame.getExecutionContext();
	services.getSpecificationRepository().addLoopInvariant(inv);

	//cache and return result
	final Instantiation result = new Instantiation(u, progPost, loop, inv, selfTerm,
	                                               innermostExecutionContext);
	lastFocusTerm = focusTerm;
	lastInstantiation = result;
	return result;
    }

    private static Term createLocalAnonUpdate(ImmutableSet<ProgramVariable> localOuts,
                                              Services services) {
        Term anonUpdate = null;
        final TermBuilder tb = services.getTermBuilder();
        for(ProgramVariable pv : localOuts) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = tb.elementary((LocationVariable)pv, tb.func(anonFunc));
            if(anonUpdate == null) {
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
    private static AnonUpdateData createAnonUpdate(LocationVariable heap, Term mod,
                                                   LoopInvariant inv, Services services) {
        final TermBuilder tb = services.getTermBuilder();
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name loopHeapName = new Name(tb.newName(heap+"_After_LOOP"));
	final Function loopHeapFunc = new Function(loopHeapName, heapLDT.targetSort(), true);
	services.getNamespaces().functions().addSafely(loopHeapFunc);

        final Term loopHeap = tb.func(loopHeapFunc);
	final Name anonHeapName = new Name(tb.newName("anon_"+heap+"_LOOP"));
	final Function anonHeapFunc = new Function(anonHeapName,heap.sort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
        final Term anonHeapTerm =
                tb.label(tb.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);

	// check for strictly pure loops
	final Term anonUpdate;
	if(tb.strictlyNothing().equals(mod)) {
	    anonUpdate = tb.skip();
	} else {
	    anonUpdate = tb.anonUpd(heap, mod, anonHeapTerm);
	}

	return new AnonUpdateData(anonUpdate, loopHeap, tb.getBaseHeap(), anonHeapTerm);
    }

    private static boolean checkFocus(final Term progPost) {
        // focus (below update) must be modality term
        return progPost.op() instanceof Modality;
    }

    private static Term buildAtPostVar(Term varTerm,
                                       String suffix,
                                       Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = new String("_" + suffix);
        }
        final String name = tb.newName(varTerm.toString() + "_After" + suffix);
        final LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        final Term varAtPost = tb.var(varAtPostVar);
        return varAtPost;
    }

    private static Term buildBeforeVar(Term varTerm,
                                       Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        final String name = tb.newName(varTerm.toString() + "_Before");
        final LocationVariable varAtPreVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPreVar, services);
        final Term varAtPre = tb.var(varAtPreVar);
        return varAtPre;
    }

    private static Term buildAfterVar(Term varTerm,
                                      Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;        

        final TermBuilder tb = services.getTermBuilder();
        final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        final String name = tb.newName(varTerm.toString() + "_After");
        final LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        final Term varAtPost = tb.var(varAtPostVar);
        return varAtPost;
    }

    private static ImmutableList<Term> buildLocalOutsAtPre(ImmutableList<Term> varTerms,
                                                           Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<Term> localOuts = ImmutableSLList.<Term>nil();
        for(final Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            final String name = tb.newName(varTerm.toString() + "_Before");
            final LocationVariable varAtPostVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final Term varAtPost = tb.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    private static ImmutableList<Term> buildLocalOutsAtPost(ImmutableList<Term> varTerms,
                                                            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<Term> localOuts = ImmutableSLList.<Term>nil();
        for(final Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            final String name = tb.newName(varTerm.toString() + "_After");
            final LocationVariable varAtPostVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final Term varAtPost = tb.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    static void register(ProgramVariable pv,
                         Services services) {
        final Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    private static void setUpInfFlowPartOfUseGoal(final InfFlowData infData,
                                                  final Term baseHeap,
                                                  Goal goal,
                                                  Services services) {
        assert infData != null;
        final TermBuilder tb = services.getTermBuilder();
        final ProofObligationVars symbExecVars = infData.symbExecVars;
        final Term heapAtPreEq =
                tb.equals(symbExecVars.pre.heap, baseHeap);
        final Term heapAtPostEq =
                tb.equals(symbExecVars.post.heap, baseHeap);
        Term beforeAssumptions = tb.and(heapAtPreEq,
                                        tb.box(infData.guardJb,
                                               tb.equals(infData.guardAtPre,
                                                         infData.guardTerm)));
        Iterator<Term> outsAtPre = infData.localOutsAtPre.iterator();
        for (Term locOut: infData.localOuts) {
            beforeAssumptions = tb.and(beforeAssumptions, tb.equals(outsAtPre.next(), locOut));
        }

        Term selfAtPostAssumption =
                // if the method is not static and if it is no constructor
                (symbExecVars.pre.self != null && symbExecVars.post.self != null) ?
                // then the self-variable does not change
                tb.equals(symbExecVars.post.self, symbExecVars.pre.self) :
                // else there is nothing to say about self
                tb.tt();
        Term afterAssumptions = tb.and(heapAtPostEq,
                                       tb.box(infData.guardJb,
                                              tb.equals(infData.guardAtPost,
                                                        infData.guardTerm)),
                                       selfAtPostAssumption);
        final Iterator<Term> outsAtPost = infData.localOutsAtPost.iterator();
        for (final Term locOut: infData.localOuts) {
            afterAssumptions = tb.and(afterAssumptions, tb.equals(outsAtPost.next(), locOut));
        }

        final Term infFlowAssumptions =
                tb.apply(infData.updates.first,
                         tb.and(beforeAssumptions,
                                 tb.apply(infData.updates.second,
                                         tb.and(afterAssumptions, infData.applPredTerm))));

        goal.addFormula(new SequentFormula(infFlowAssumptions),
                        true,
                        false);
        goal.addTaclet(infData.infFlowApp,
                       SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        goal.proof().addIFSymbol(infData.applPredTerm);
        goal.proof().addIFSymbol(infData.infFlowApp);
        goal.proof().addGoalTemplates(infData.infFlowApp);
    }

    private static InfFlowData setUpInfFlowValidityGoal(Goal infFlowGoal,
                                                        LoopInvariantBuiltInRuleApp ruleApp,
                                                        final Instantiation inst,
                                                        final JavaBlock guardJb,
                                                        final ImmutableSet<ProgramVariable> localIns,
                                                        final ImmutableSet<ProgramVariable> localOuts,
                                                        final ImmutableList<AnonUpdateData> anonUpdateDatas,
                                                        final Term anonUpdate,
                                                        Services services)
            throws RuleAbortException {
        assert anonUpdateDatas.size() == 1 : "information flow " +
                                             "extension is at the " +
                                             "moment not compatible " +
                                             "with the non-base-heap " +
                                             "setting";
        final AnonUpdateData anonUpdateData = anonUpdateDatas.head();
        final TermBuilder tb = services.getTermBuilder();

        // reset validiy branch
        infFlowGoal.setBranchLabel("Information Flow Validity");

        // clear goal
        infFlowGoal.node().setSequent(Sequent.EMPTY_SEQUENT);
        infFlowGoal.clearAndDetachRuleAppIndex();

        // prepare data
        LoopInvariant inv = inst.inv;
        final Term guard = ruleApp.getGuard();
        InfFlowData infFlowData =
                prepareSetUpOfInfFlowValidityGoal(anonUpdateData, guard,
                                                  inst, inv, services, ruleApp,
                                                  localIns, localOuts,
                                                  anonUpdate, guardJb);

        // generate information flow proof obligation variables
        final IFProofObligationVars ifVars =
                new IFProofObligationVars(infFlowData.symbExecVars, services);
        ruleApp.setInformationFlowProofObligationVars(ifVars);

        // set execution context
        ruleApp.setExecutionContext(inst.innermostExecutionContext);

        // create proof obligation
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(inv, ifVars.c1, ifVars.c2,
                                                   inst.innermostExecutionContext,
                                                   guard, services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
        final Term post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);

        final Term finalTerm =
                tb.imp(tb.label(selfComposedExec, ParameterlessTermLabel.SELF_COMPOSITION_LABEL),
                       post);
        infFlowGoal.proof().addLabeledIFSymbol(selfComposedExec);
        infFlowGoal.addFormula(new SequentFormula(finalTerm), false, true);

        return infFlowData;
    }

    //-------------------------------------------------------------------------
    // helper methods for apply()
    //-------------------------------------------------------------------------

    private Term conjunctInv(Services services, Instantiation inst,
                             final Map<LocationVariable, Term> atPres,
                             final List<LocationVariable> heapContext) {
        Term invTerm = null;
        for(LocationVariable heap : heapContext) {
            final Term i = inst.inv.getInvariant(heap, inst.selfTerm, atPres, services);
            if(i == null) continue;
            if(invTerm == null) {
                invTerm = i;
            }else{
                invTerm = services.getTermBuilder().and(invTerm, i);
            }
        }
        return invTerm;
    }

    private Pair<Term,Term> prepareVariant (Instantiation inst, Term variant, TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final ProgramElementName variantName 
            = new ProgramElementName(tb.newName("variant"));
        final LocationVariable variantPV = new LocationVariable(variantName, Sort.ANY);
        services.getNamespaces().programVariables().addSafely(variantPV);

        final boolean dia = ((Modality)inst.progPost.op()).terminationSensitive();
        final Term variantUpdate 
            = dia ? tb.elementary(variantPV, variant) : tb.skip();
        final Term variantPO = dia ? tb.prec(variant, tb.var(variantPV)) : tb.tt();
        return new Pair<Term,Term> (variantUpdate,variantPO);
    }


    private Term bodyTerm(Services services, RuleApp ruleApp,
                          final Sequent applicationSequent, Instantiation inst,
                          final Term invTerm, Term frameCondition, final Term variantPO,
                          Goal bodyGoal, final JavaBlock guardJb, final Term guardTrueTerm) {
        final WhileInvariantTransformer wir = new WhileInvariantTransformer();
        final TermBuilder tb = services.getTermBuilder();
        SVInstantiations svInst =
                SVInstantiations.EMPTY_SVINSTANTIATIONS.replace(null,
                                                                null,
                                                                inst.innermostExecutionContext,
                                                                null,
                                                                services);
        for(SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
            assert sv instanceof ProgramSV;
            svInst = svInst.addInteresting(sv, 
                    (Name) new ProgramElementName(sv.name().toString()), 
                    services);
        }
        Term fullInvariant = tb.and(invTerm, frameCondition, variantPO);
        fullInvariant = TermLabelManager.refactorTerm(services, null, fullInvariant, this, bodyGoal, FULL_INVARIANT_TERM_HINT, null);
        Term bodyTerm = wir.transform(this, bodyGoal, applicationSequent,
                                      ruleApp.posInOccurrence(), inst.progPost,
                                      fullInvariant,
                                      svInst, services);
        final Term guardTrueBody = tb.imp(tb.box(guardJb,guardTrueTerm), bodyTerm);
        return guardTrueBody;
    }


    private SequentFormula initFormula(Instantiation inst, 
                                       final Term invTerm,
                                       Term reachableState, 
                                       Services services,
                                       Goal initGoal) {
        final TermBuilder tb = services.getTermBuilder();
        Term sfTerm = tb.apply(inst.u, tb.and(invTerm, reachableState), null);
        sfTerm = TermLabelManager.refactorTerm(services, null, sfTerm, this, initGoal, INITIAL_INVARIANT_ONLY_HINT, null);
        return new SequentFormula(sfTerm);
    }

    private Term useCaseFormula(Services services, RuleApp ruleApp,
                                Instantiation inst, Goal useGoal, final JavaBlock guardJb,
                                final Term guardFalseTerm) {
        final TermBuilder tb = services.getTermBuilder();
        JavaBlock useJavaBlock = JavaTools.removeActiveStatement(inst.progPost.javaBlock(), services);
        final ImmutableArray<TermLabel> instantiateLabels =
                TermLabelManager.instantiateLabels(services, ruleApp.posInOccurrence(), this, useGoal,
                                                   "UseModality", null, inst.progPost.op(),
                                                   new ImmutableArray<Term>(inst.progPost.sub(0)),
                                                   null, useJavaBlock);
        Term restPsi = tb.prog((Modality)inst.progPost.op(), useJavaBlock, inst.progPost.sub(0),
                               instantiateLabels);
        Term guardFalseRestPsi = tb.box(guardJb, tb.imp(guardFalseTerm, restPsi));
        return guardFalseRestPsi;
    }

    private Triple<JavaBlock, Term, Term> prepareGuard(final Instantiation inst,
                                                       final KeYJavaType booleanKJT,
                                                       LoopInvariantBuiltInRuleApp loopRuleApp,
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
        final Statement guardVarMethodFrame =
                inst.innermostExecutionContext == null ?
                        guardVarDecl : new MethodFrame(null, inst.innermostExecutionContext,
                                                       new StatementBlock(guardVarDecl));
        final JavaBlock guardJb =
                JavaBlock.createJavaBlock(new StatementBlock(guardVarMethodFrame));
        final Term guardTrueTerm = tb.equals(tb.var(guardVar), tb.TRUE());
        final Term guardFalseTerm = tb.equals(tb.var(guardVar), tb.FALSE());
        return new Triple<JavaBlock, Term, Term>(guardJb,guardTrueTerm,guardFalseTerm);
    }

    private void prepareInvInitiallyValidBranch(Services services,
                                                RuleApp ruleApp,
                                                Instantiation inst,
                                                final Term invTerm,
                                                Term reachableState,
                                                Goal initGoal) {
        initGoal.setBranchLabel("Invariant Initially Valid");
        initGoal.changeFormula(initFormula(inst, invTerm, reachableState, services, initGoal),
                               ruleApp.posInOccurrence());
        TermLabelManager.refactorLabels(services, ruleApp.posInOccurrence(), this, initGoal, null, null);
    }


    private void prepareBodyPreservesBranch(Services services,
                                            RuleApp ruleApp,
                                            final Sequent applicationSequent,
                                            Instantiation inst,
                                            final Term invTerm,
                                            Term wellFormedAnon,
                                            Term frameCondition,
                                            final Term variantPO,
                                            Goal bodyGoal,
                                            final JavaBlock guardJb,
                                            final Term guardTrueTerm,
                                            final Term[] uBeforeLoopDefAnonVariant,
                                            final Term uAnonInv) {
        final TermBuilder tb = services.getTermBuilder();
        bodyGoal.setBranchLabel("Body Preserves Invariant");
        bodyGoal.addFormula(new SequentFormula(wellFormedAnon), 
                true, 
                false);         

        bodyGoal.addFormula(new SequentFormula(uAnonInv), 
                true, 
                false);

        Term guardTrueBody = bodyTerm(services, ruleApp, applicationSequent,
                                      inst, invTerm, frameCondition, variantPO,
                                      bodyGoal, guardJb, guardTrueTerm); 

        bodyGoal.changeFormula(new SequentFormula(tb.applySequential(uBeforeLoopDefAnonVariant, 
                                                                     guardTrueBody)), 
                                                  ruleApp.posInOccurrence());
    }


    private void prepareUseCaseBranch(Services services, RuleApp ruleApp,
                                      Instantiation inst, Term wellFormedAnon,
                                      Goal useGoal, final JavaBlock guardJb,
                                      final Term guardFalseTerm,
                                      final Term[] uAnon, final Term uAnonInv) {
        useGoal.setBranchLabel("Use Case");
        useGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
        useGoal.addFormula(new SequentFormula(uAnonInv), true, false);
        final TermBuilder tb = services.getTermBuilder();

        Term guardFalseRestPsi = useCaseFormula(services, ruleApp, inst, useGoal, guardJb, guardFalseTerm);
        useGoal.changeFormula(new SequentFormula(tb.applySequential(uAnon, guardFalseRestPsi)),
                              ruleApp.posInOccurrence());
    }
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return checkApplicability(goal,pio);
    }


    //focus must be top level succedent
    static boolean checkApplicability (Goal g, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }
        Pair<Term, Term> up = applyUpdates(pio.subTerm(), g.proof().getServices());
        final Term progPost = up.second;
        if (!checkFocus(progPost)) {
            return false;
        }
        // active statement must be while loop
        final SourceElement activeStatement = JavaTools.getActiveStatement(progPost.javaBlock());
        if (!(activeStatement instanceof While)) {
            return false;
        }
        return true;
    }

    static Pair<Term, Term> applyUpdates(Term focusTerm, TermServices services) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm),
                    UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<Term, Term>(services.getTermBuilder().skip(), focusTerm);
        }
    }

    private void setupWdGoal(final Goal goal, final LoopInvariant inv,
                             final Term update, final Term selfTerm,
                             final LocationVariable heap, final Term anonHeap,
                             final ImmutableSet<ProgramVariable> localIns,
                             PosInOccurrence pio, Services services) {
        if (goal == null) {
            return;
        }
        goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
        final LoopWellDefinedness lwd =  new LoopWellDefinedness(inv, localIns, services);
        final ProgramVariable self;
        if(selfTerm != null && selfTerm.op() instanceof ProgramVariable) {
            self = (ProgramVariable)selfTerm.op();
        } else {
            self = null;
        }
        services.getSpecificationRepository().addWdStatement(lwd);
        final SequentFormula wdInv = lwd.generateSequent(self, heap, anonHeap, localIns,
                                                         update, services);
        goal.changeFormula(wdInv, pio);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, final RuleApp ruleApp)
            throws RuleAbortException {
        assert ruleApp instanceof LoopInvariantBuiltInRuleApp;
        LoopInvariantBuiltInRuleApp loopRuleApp = (LoopInvariantBuiltInRuleApp) ruleApp;
        final Sequent applicationSequent = goal.sequent();
        final KeYJavaType booleanKJT = services.getTypeConverter().getBooleanType();
        final TermBuilder tb = services.getTermBuilder();

        //get instantiation
        final Instantiation inst = instantiate(loopRuleApp, services);

        final Map<LocationVariable,Term> atPres = inst.inv.getInternalAtPres();
        final List<LocationVariable> heapContext = ((IBuiltInRuleApp)ruleApp).getHeapContext();        

        final Term invTerm = conjunctInv(services, inst, atPres, heapContext);

        final Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : heapContext) {
            final Term m = inst.inv.getModifies(heap, inst.selfTerm, atPres, services);
            mods.put(heap, m);
        }

        final Term variant = inst.inv.getVariant(inst.selfTerm, atPres, services);

        //collect input and output local variables, 
        //prepare reachableIn and reachableOut
        final ImmutableSet<ProgramVariable> localIns =
                MiscTools.getLocalIns(inst.loop, services);
        final ImmutableSet<ProgramVariable> localOuts =
                MiscTools.getLocalOuts(inst.loop, services);
        Term reachableIn = tb.tt();
        for(ProgramVariable pv : localIns) {
            reachableIn = tb.and(reachableIn, 
                                 tb.reachableValue(pv));
        }
        Term reachableOut = tb.tt();

        for(ProgramVariable pv : localOuts) {
            reachableOut = tb.and(reachableOut, 
                    tb.reachableValue(pv));
        }

        //prepare variant
        final Pair<Term,Term> variantPair = prepareVariant(inst, variant, services);
        final Term variantUpdate = variantPair.first;
        final Term variantPO = variantPair.second;
        
        //prepare guard
        final Triple<JavaBlock,Term,Term> guardStuff =
                prepareGuard(inst, booleanKJT, loopRuleApp, services);
        final JavaBlock guardJb = guardStuff.first;
        final Term guardTrueTerm = guardStuff.second;
        final Term guardFalseTerm = guardStuff.third;

        Term beforeLoopUpdate = null;

        final Map<LocationVariable,Map<Term,Term>> heapToBeforeLoop =
                new LinkedHashMap<LocationVariable,Map<Term,Term>>();

        for(LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<Term,Term>());
            final LocationVariable lv =
                    tb.heapAtPreVar(heap+"Before_LOOP", heap.sort(), true);
            services.getNamespaces().programVariables().addSafely(lv);
            final Term u = tb.elementary(lv, tb.var(heap));
            if (beforeLoopUpdate == null) {
                beforeLoopUpdate = u;
            } else {
                beforeLoopUpdate = tb.parallel(beforeLoopUpdate, u);
            }
            heapToBeforeLoop.get(heap).put(tb.var(heap), tb.var(lv));
        }

        for (ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName
            = tb.newName(pv.name().toString() + "Before_LOOP");
            final LocationVariable pvBeforeLoop
            = new LocationVariable(new ProgramElementName(pvBeforeLoopName), pv.getKeYJavaType());
            services.getNamespaces().programVariables().addSafely(pvBeforeLoop);
            beforeLoopUpdate = tb.parallel(beforeLoopUpdate,
                                           tb.elementary(pvBeforeLoop, 
                                                         tb.var(pv)));
            heapToBeforeLoop.get(services.getTypeConverter().getHeapLDT().getHeap())
                    .put(tb.var(pv), tb.var(pvBeforeLoop));
        }

        //prepare anon update, frame condition, etc.
        Term anonUpdate = createLocalAnonUpdate(localOuts, services); // can still be null
        //Term anonAssumption = null;
        Term wellFormedAnon = null;
        Term frameCondition = null;
        Term reachableState = null;
        Term anonHeap = null;
        ImmutableList<AnonUpdateData> anonUpdateDatas =
                ImmutableSLList.<AnonUpdateData>nil();
        for (LocationVariable heap : heapContext) {
            final AnonUpdateData tAnon
            = createAnonUpdate(heap, mods.get(heap), inst.inv, services);
            anonUpdateDatas = anonUpdateDatas.append(tAnon);
            if(anonUpdate == null) {
                anonUpdate = tAnon.anonUpdate;
            } else{
                anonUpdate = tb.parallel(anonUpdate, tAnon.anonUpdate);
            }
            if(wellFormedAnon == null) {
                wellFormedAnon = tb.wellFormed(tAnon.anonHeap);
            } else{
                wellFormedAnon = tb.and(wellFormedAnon, tb.wellFormed(tAnon.anonHeap));
            }
            if (anonHeap == null) {
                anonHeap = tAnon.anonHeap;
            }
            final Term m = mods.get(heap);
            final Term fc;
          if (tb.strictlyNothing().equals(m)) {
                fc = tb.frameStrictlyEmpty(tb.var(heap), heapToBeforeLoop.get(heap)); 
            } else{
                fc = tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), m);
            }
            if(frameCondition == null){
                frameCondition = fc;
            } else{
                frameCondition = tb.and(frameCondition, fc);
            }
            if (reachableState == null) {
                reachableState = tb.wellFormed(heap);
              } else {
                reachableState = tb.and(reachableState, tb.wellFormed(heap));
              }
        }

        //prepare common assumption
        final Term[] uAnon 
        = new Term[]{inst.u, anonUpdate};
        final Term[] uBeforeLoopDefAnonVariant =
                new Term[]{inst.u,
                           beforeLoopUpdate,
                           anonUpdate,
                           variantUpdate};
        final Term uAnonInv = tb.applySequential(uAnon, tb.and(invTerm, reachableOut));

        final ImmutableList<Goal> result;
        Goal wdGoal;
        if (WellDefinednessCheck.isOn()) {
            //split goal into four branches
            result = goal.split(4);
            wdGoal = result.tail().tail().tail().head();
            wdGoal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
        } else {
            //split goal into three branches
            result = goal.split(3);
            wdGoal = null;
        }
        Goal initGoal = result.tail().tail().head();
        Goal bodyGoal = result.tail().head();
        Goal useGoal = result.head();

        //"Invariant Initially Valid":
        // \replacewith (==> inv );
        prepareInvInitiallyValidBranch(services, ruleApp, inst, invTerm, reachableState, initGoal);

        setupWdGoal(wdGoal, inst.inv, inst.u, inst.selfTerm, heapContext.get(0),
                    anonHeap, localIns, ruleApp.posInOccurrence(), services);

        //"Body Preserves Invariant":
        // \replacewith (==>  #atPreEqs(anon1) 
        //                       -> #introNewAnonUpdate(#modifies, #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv -> 
        //                         (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
        //                          #whileInvRule(\[{.. while (#e) #s ...}\]post,
        //                               #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post)
        //                                  & inv)),
        //                          anon1));
        prepareBodyPreservesBranch(services, ruleApp, applicationSequent, inst,
                                   invTerm, wellFormedAnon, frameCondition,
                                   variantPO, bodyGoal, guardJb, guardTrueTerm,
                                   uBeforeLoopDefAnonVariant, uAnonInv);

        if (InfFlowCheckInfo.isInfFlow(goal) && inst.inv.hasInfFlowSpec(services)) {
            // set up information flow validity goal
            InfFlowData infFlowData =
                    setUpInfFlowValidityGoal(bodyGoal, loopRuleApp, inst,
                                             guardJb, localIns, localOuts,
                                             anonUpdateDatas, anonUpdate,
                                             services);

            // set up information flow part of useGoal:
            // add infFlowAssumptions, add term and taclet to post goal
            setUpInfFlowPartOfUseGoal(infFlowData,
                                      anonUpdateDatas.head().loopHeapAtPre,
                                      useGoal, services);
        }

        //"Invariant Initially Valid":
        // \replacewith (==> inv );
        prepareInvInitiallyValidBranch(services, ruleApp, inst, invTerm, reachableState, initGoal);

        setupWdGoal(wdGoal, inst.inv, inst.u, inst.selfTerm, heapContext.get(0),
                    anonHeap, localIns, ruleApp.posInOccurrence(), services);

        // "Use Case":
        // \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
        // (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
        // (#v1=FALSE -> \[{.. ...}\]post)),anon2))
        prepareUseCaseBranch(services, ruleApp, inst, wellFormedAnon, useGoal,
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

    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------

    private static final class Instantiation {
	public final Term u;
	public final Term progPost;
	public final While loop;
	public final LoopInvariant inv;
	public final Term selfTerm;
	public final ExecutionContext innermostExecutionContext;

	public Instantiation(Term u, 
			     Term progPost, 
			     While loop,
			     LoopInvariant inv,
			     Term selfTerm,
			     ExecutionContext innermostExecutionContext) {
	    assert u != null;
	    assert u.sort() == Sort.UPDATE;
	    assert progPost != null;
	    assert progPost.sort() == Sort.FORMULA;
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
        public final Term anonUpdate, anonHeap, loopHeap, loopHeapAtPre;

        public AnonUpdateData(Term anonUpdate,
                              Term loopHeap,
                              Term loopHeapAtPre,
                              Term anonHeap) {
            this.anonUpdate = anonUpdate;
            this.loopHeap = loopHeap;
            this.loopHeapAtPre = loopHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }

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

        private InfFlowData(ProofObligationVars symbExecVars,
                            Term guardAtPre,
                            Term guardAtPost,
                            JavaBlock guardJb,
                            Term guardTerm,
                            ImmutableList<Term> localOuts,
                            ImmutableList<Term> localOutsAtPre,
                            ImmutableList<Term> localOutsAtPost,
                            Pair<Term, Term> updates,
                            Term applPredTerm,
                            Taclet infFlowApp) {
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
