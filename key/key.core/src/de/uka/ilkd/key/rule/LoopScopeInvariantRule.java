package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.LoopScopeBlock;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
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
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.ReplaceWhileLoop;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class LoopScopeInvariantRule implements BuiltInRule {
    /**
     * The Singleton instance of {@link LoopScopeInvariantRule}.
     */
    public static final LoopScopeInvariantRule INSTANCE = new LoopScopeInvariantRule();

    /**
     * The hint used to refactor the initial invariant.
     */
    public static final String INITIAL_INVARIANT_ONLY_HINT = "onlyInitialInvariant";

    /**
     * The hint used to refactor the full invariant.
     */
    public static final String FULL_INVARIANT_TERM_HINT = "fullInvariant";

    private static final Name NAME = new Name("Loop (Scope) Invariant");

    /**
     * TODO
     */
    private static Term lastFocusTerm;

    /**
     * TODO
     */
    private static Instantiation lastInstantiation;

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        // Initial assertions
        assert ruleApp instanceof LoopInvariantBuiltInRuleApp;

        // Basic objects needed for rule application
        final TermBuilder tb = services.getTermBuilder();
        final TermLabelState termLabelState = new TermLabelState();
        final LoopInvariantBuiltInRuleApp loopRuleApp = (LoopInvariantBuiltInRuleApp) ruleApp;

        // Prepare the new goals
        ImmutableList<Goal> goals = goal.split(3);
        Goal initiallyGoal = goals.tail().tail().head();
        Goal preservesGoal = goals.tail().head();
        Goal useCaseGoal = goals.head();

        // Get the Instantiation object
        final Instantiation inst = instantiate(loopRuleApp, services);

        // Get necessary parts of invariant and sequent
        final Map<LocationVariable, Term> atPres = inst.inv.getInternalAtPres();
        final List<LocationVariable> heapContext = ((IBuiltInRuleApp) ruleApp)
                .getHeapContext();

        final Term invTerm = conjunctInv(services, inst, atPres, heapContext);
        final Term invFreeTerm = conjunctFreeInv(services, inst, atPres,
                heapContext);

        final Map<LocationVariable, Term> mods = new LinkedHashMap<LocationVariable, Term>();
        heapContext.forEach(heap -> mods.put(heap,
                inst.inv.getModifies(heap, inst.selfTerm, atPres, services)));

        // Collect input and output local variables,
        // prepare reachableOut.
        // TODO: reachableIn has been removed since it was not even used in the
        // old invariant rule. Is that OK or was there an earlier mistake?
        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(inst.loop, services);

        final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoop = //
                new LinkedHashMap<LocationVariable, Map<Term, Term>>();

        // prepare anon update, frame condition, etc.
        // can still be null
        Term anonUpdate = createLocalAnonUpdate(localOuts, services);
        if (anonUpdate == null) {
            anonUpdate = tb.skip();
        }

        // Create update for values before loop
        Term beforeLoopUpdate = createBeforeLoopUpdate(services, heapContext,
                localOuts, heapToBeforeLoop);

        Term wellFormedAnon = null;
        Term frameCondition = null;
        Term reachableState = null;

        for (LocationVariable heap : heapContext) {
            final AnonUpdateData tAnon = createAnonUpdate(heap, mods.get(heap),
                    inst.inv, services);

            anonUpdate = tb.parallel(anonUpdate, tAnon.anonUpdate);

            wellFormedAnon = and(tb, wellFormedAnon,
                    tb.wellFormed(tAnon.anonHeap));

            final Term m = mods.get(heap);
            final Term fc;

            if (tb.strictlyNothing().equals(m)) {
                fc = tb.frameStrictlyEmpty(tb.var(heap),
                        heapToBeforeLoop.get(heap));
            } else {
                fc = tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), m);
            }

            frameCondition = and(tb, frameCondition, fc);
            reachableState = and(tb, reachableState, tb.wellFormed(heap));
        }

        // Prepare variant
        final Term variant = //
                inst.inv.getVariant(inst.selfTerm, atPres, services);
        final Pair<Term, Term> variantPair = prepareVariant(inst, variant,
                services);
        final Term variantUpdate = variantPair.first;
        final Term variantPO = variantPair.second;

        // Prepare common assumption
        final Term reachableOut = localOuts.stream()
                .map(pv -> tb.reachableValue(pv))
                .reduce(tb.tt(), (Term acc, Term term) -> tb.and(acc, term));

        final Term[] uAnon = new Term[] { inst.u, anonUpdate };
        final Term[] uBeforeLoopDefAnonVariant = new Term[] { inst.u,
                beforeLoopUpdate, anonUpdate, variantUpdate };
        final Term uAnonInv = tb.applySequential(uAnon,
                tb.and(tb.and(invTerm, reachableOut), invFreeTerm));

        // Create the "Initially" goal
        constructInitiallyGoal(services, ruleApp, termLabelState, initiallyGoal,
                inst, invTerm, reachableState);

        // Create the "Invariant Preserved" goal
        constructPresrvAndUCGoal(services, ruleApp, tb, preservesGoal, inst,
                anonUpdate, wellFormedAnon, uAnonInv, frameCondition, variantPO,
                termLabelState, invTerm, uBeforeLoopDefAnonVariant);

        // "Use Case":
        // \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
        // (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
        // (#v1=FALSE -> \[{.. ...}\]post)),anon2))
        final Triple<JavaBlock, Term, Term> guardStuff = prepareGuard(inst,
                services.getTypeConverter().getBooleanType(), loopRuleApp,
                services);

        prepareUseCaseBranch(termLabelState, services, ruleApp, inst,
                wellFormedAnon, useCaseGoal, guardStuff.first, guardStuff.third, uAnon,
                uAnonInv);

        return goals;
    }

    /**
     * Sets the content of the "initially valid" goal.
     * 
     * @param services
     *            The {@link Services} object.
     * @param ruleApp
     *            The {@link RuleApp} for this {@link LoopScopeInvariantRule}
     *            application.
     * @param termLabelState
     * @param initiallyGoal
     * @param inst
     * @param invTerm
     * @param reachableState
     */
    private void constructInitiallyGoal(Services services, RuleApp ruleApp,
            final TermLabelState termLabelState, Goal initiallyGoal,
            final Instantiation inst, final Term invTerm, Term reachableState) {
        initiallyGoal.setBranchLabel("Invariant Initially Valid");
        initiallyGoal
                .changeFormula(
                        initFormula(termLabelState, inst, invTerm,
                                reachableState, services, initiallyGoal),
                        ruleApp.posInOccurrence());
    }

    /**
     * TODO
     * 
     * @param services
     * @param tb
     * @param heapContext
     * @param localOuts
     * @param heapToBeforeLoop
     * @return
     */
    private Term createBeforeLoopUpdate(Services services,
            final List<LocationVariable> heapContext,
            final ImmutableSet<ProgramVariable> localOuts,
            final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoop) {
        final TermBuilder tb = services.getTermBuilder();
        final Namespace progVarNS = services.getNamespaces().programVariables();

        Term beforeLoopUpdate = null;
        for (LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<Term, Term>());
            final LocationVariable lv = tb.heapAtPreVar(heap + "Before_LOOP",
                    heap.sort(), true);
            progVarNS.addSafely(lv);

            final Term u = tb.elementary(lv, tb.var(heap));
            if (beforeLoopUpdate == null) {
                beforeLoopUpdate = u;
            } else {
                beforeLoopUpdate = tb.parallel(beforeLoopUpdate, u);
            }

            heapToBeforeLoop.get(heap).put(tb.var(heap), tb.var(lv));
        }

        for (ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName = tb
                    .newName(pv.name().toString() + "Before_LOOP");
            final LocationVariable pvBeforeLoop = new LocationVariable(
                    new ProgramElementName(pvBeforeLoopName),
                    pv.getKeYJavaType());
            progVarNS.addSafely(pvBeforeLoop);
            beforeLoopUpdate = tb.parallel(beforeLoopUpdate,
                    tb.elementary(pvBeforeLoop, tb.var(pv)));
            heapToBeforeLoop
                    .get(services.getTypeConverter().getHeapLDT().getHeap())
                    .put(tb.var(pv), tb.var(pvBeforeLoop));
        }

        return beforeLoopUpdate;
    }

    /**
     * TODO
     * 
     * @param services
     * @param ruleApp
     * @param tb
     * @param presrvAndUCGoal
     * @param inst
     * @param anonUpdate
     * @param uAnonInv
     * @param frameCondition
     * @param variantPO
     * @param termLabelState
     * @param invTerm
     * @param uBeforeLoopDefAnonVariant
     */
    private void constructPresrvAndUCGoal(Services services, RuleApp ruleApp,
            final TermBuilder tb, Goal presrvAndUCGoal,
            final Instantiation inst, Term anonUpdate, Term wellFormedAnon,
            final Term uAnonInv, Term frameCondition, Term variantPO,
            TermLabelState termLabelState, Term invTerm,
            Term[] uBeforeLoopDefAnonVariant) {
        final While loop = inst.loop;

        final Term newFormula = formulaWithLoopScope(services, inst, anonUpdate,
                loop, frameCondition, variantPO, termLabelState,
                presrvAndUCGoal, uBeforeLoopDefAnonVariant, invTerm);

        presrvAndUCGoal.setBranchLabel("Invariant Preserved");
        presrvAndUCGoal.addFormula(new SequentFormula(uAnonInv), true, false);
        presrvAndUCGoal.addFormula(new SequentFormula(wellFormedAnon), true,
                false);
        presrvAndUCGoal.changeFormula(new SequentFormula(newFormula),
                ruleApp.posInOccurrence());
    }

    /**
     * 
     * TODO
     * 
     * @param inst
     * @param booleanKJT
     * @param loopRuleApp
     * @param services
     * @return
     */
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

    /**
     * TODO
     * 
     * @param termLabelState
     * @param services
     * @param ruleApp
     * @param inst
     * @param wellFormedAnon
     * @param useGoal
     * @param guardJb
     * @param guardFalseTerm
     * @param uAnon
     * @param uAnonInv
     */
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

    /**
     * TODO
     * 
     * @param termLabelState
     * @param services
     * @param ruleApp
     * @param inst
     * @param useGoal
     * @param guardJb
     * @param guardFalseTerm
     * @return
     */
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

    /**
     * TODO
     * 
     * @param services
     * @param inst
     * @param anonUpdate
     * @param loop
     * @param frameCondition
     * @param variantPO
     * @param termLabelState
     * @param presrvAndUCGoal
     * @param invTerm
     * @return
     */
    private Term formulaWithLoopScope(Services services,
            final Instantiation inst, Term anonUpdate, final While loop,
            Term frameCondition, Term variantPO, TermLabelState termLabelState,
            Goal presrvAndUCGoal, final Term[] uBeforeLoopDefAnonVariant,
            Term invTerm) {
        final TermBuilder tb = services.getTermBuilder();
        final Term progPost = splitUpdates(inst.progPost, services).second;

        Term fullInvariant = tb.and(invTerm, frameCondition, variantPO);
        fullInvariant = TermLabelManager.refactorTerm(termLabelState, services,
                null, fullInvariant, this, presrvAndUCGoal,
                FULL_INVARIANT_TERM_HINT, null);

        final Term post = progPost.sub(0);
        final Modality modality = (Modality) progPost.op();
        final JavaBlock origJavaBlock = progPost.javaBlock();

        final ProgramVariable loopScopeIdxVar = loopScopeIdxVar(services);

        final ProgramElement newProg = newProgram(services, loop, origJavaBlock,
                loopScopeIdxVar);

        final Term newPost = tb.and(
                tb.imp(tb.equals(tb.var(loopScopeIdxVar), tb.TRUE()), post),
                tb.imp(tb.equals(tb.var(loopScopeIdxVar), tb.FALSE()),
                        fullInvariant));

        final Term newFormula = tb.applySequential(uBeforeLoopDefAnonVariant,
                tb.prog(modality,
                        JavaBlock.createJavaBlock((StatementBlock) newProg),
                        newPost));
        return newFormula;
    }

    /**
     * TODO
     * 
     * @param services
     * @return
     */
    private ProgramVariable loopScopeIdxVar(Services services) {
        final KeYJavaType booleanType = services.getJavaInfo()
                .getKeYJavaType("boolean");

        final ProgramVariable loopScopeIdxVar = //
                KeYJavaASTFactory
                        .localVariable( //
                                services.getVariableNamer()
                                        .getTemporaryNameProposal("x"),
                                booleanType);

        return loopScopeIdxVar;
    }

    /**
     * TODO
     * 
     * @param services
     * @param loop
     * @param progPost
     * @param loopScopeIdxVar
     * @return
     */
    private ProgramElement newProgram(Services services, final While loop,
            final JavaBlock origProg, final ProgramVariable loopScopeIdxVar) {
        final ArrayList<ProgramElement> stmnt = new ArrayList<ProgramElement>();

        ((StatementBlock) loop.getBody()).getBody()
                .forEach(elem -> stmnt.add(elem));
        stmnt.add(KeYJavaASTFactory.continueStatement(null));

        final Statement newIf = KeYJavaASTFactory.ifThen(
                loop.getGuardExpression(),
                new StatementBlock(stmnt.toArray(new Statement[stmnt.size()])));

        LoopScopeBlock loopScope = new LoopScopeBlock(loopScopeIdxVar,
                KeYJavaASTFactory.block(newIf));

        final ReplaceWhileLoop rplLoopVisitor = new ReplaceWhileLoop(
                origProg.program(),
                KeYJavaASTFactory.block(KeYJavaASTFactory.declare(
                        loopScopeIdxVar, KeYJavaASTFactory.falseLiteral()),
                        loopScope),
                services);
        rplLoopVisitor.start();

        return rplLoopVisitor.result();
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

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()
                || Transformer.inTransformer(pio)) {
            return false;
        }

        final Term progPost = splitUpdates(pio.subTerm(),
                goal.proof().getServices()).second;

        // active statement must be while loop
        JavaBlock javaBlock = progPost.javaBlock();

        return !javaBlock.isEmpty()
                && JavaTools.getActiveStatement(javaBlock) instanceof While;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new LoopInvariantBuiltInRuleApp(this, pos, services);
    }

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private LoopScopeInvariantRule() {
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * TODO
     * 
     * @param progPost
     * @return
     */
    private static boolean isModalityTerm(final Term progPost) {
        // focus (below update) must be modality term
        // TODO isn't that the same as !progPost.javaBlock().isEmpty() ?
        return progPost.op() instanceof Modality;
    }

    /**
     * TODO
     * 
     * @param localOuts
     * @param services
     * @return
     */
    private static Term createLocalAnonUpdate(
            ImmutableSet<ProgramVariable> localOuts, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        return localOuts.stream().map(pv -> {
            final Function anonFunc = new Function(
                    new Name(tb.newName(pv.name().toString())), pv.sort(),
                    true);
            services.getNamespaces().functions().addSafely(anonFunc);

            return tb.elementary((LocationVariable) pv, tb.func(anonFunc));
        }).reduce(tb.skip(), (acc, t) -> tb.parallel(acc, t));
    }

    /**
     * TODO
     * 
     * @return (assumption, anon update, anon heap)
     */
    private static AnonUpdateData createAnonUpdate(LocationVariable heap,
            Term mod, LoopSpecification inv, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final Name loopHeapName = new Name(tb.newName(heap + "_After_LOOP"));
        final Function loopHeapFunc = new Function(loopHeapName,
                heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(loopHeapFunc);

        final Term loopHeap = tb.func(loopHeapFunc);
        final Name anonHeapName = new Name(
                tb.newName("anon_" + heap + "_LOOP"));
        final Function anonHeapFunc = new Function(anonHeapName, heap.sort());
        services.getNamespaces().functions().addSafely(anonHeapFunc);
        final Term anonHeapTerm = tb.label(tb.func(anonHeapFunc),
                ParameterlessTermLabel.ANON_HEAP_LABEL);

        // check for strictly pure loops
        final Term anonUpdate;
        if (tb.strictlyNothing().equals(mod)) {
            anonUpdate = tb.skip();
        } else {
            anonUpdate = tb.anonUpd(heap, mod, anonHeapTerm);
        }

        return new AnonUpdateData( //
                anonUpdate, loopHeap, //
                tb.getBaseHeap(), anonHeapTerm);
    }

    /**
     * TODO
     * 
     * @param focusTerm
     * @param services
     * @return
     */
    private static Pair<Term, Term> splitUpdates(Term focusTerm,
            TermServices services) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm),
                    UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<Term, Term>(services.getTermBuilder().skip(),
                    focusTerm);
        }
    }

    /**
     * TODO
     * 
     * @param app
     * @param services
     * @return
     * @throws RuleAbortException
     */
    private static Instantiation instantiate(
            final LoopInvariantBuiltInRuleApp app, Services services)
            throws RuleAbortException {
        final Term focusTerm = app.posInOccurrence().subTerm();

        if (focusTerm == lastFocusTerm && lastInstantiation.inv == services
                .getSpecificationRepository()
                .getLoopSpec(lastInstantiation.loop)) {
            return lastInstantiation;
        }

        // leading update?
        final Pair<Term, Term> update = splitUpdates(focusTerm, services);
        final Term u = update.first;
        final Term progPost = update.second;

        // focus (below update) must be modality term
        if (!isModalityTerm(progPost)) {
            return null;
        }

        // active statement must be while loop
        final While loop = app.getLoopStatement();

        // try to get invariant from JML specification
        LoopSpecification spec = app.getSpec();
        if (spec == null) { // may happen after reloading proof
            throw new RuleAbortException(
                    "No invariant found. Probably broken after proof reloading...");
        }

        // collect self, execution context
        final MethodFrame innermostMethodFrame = JavaTools
                .getInnermostMethodFrame(progPost.javaBlock(), services);
        if (innermostMethodFrame != null) {
            spec = spec.setTarget(innermostMethodFrame.getProgramMethod());
        }

        final Term selfTerm = innermostMethodFrame == null ? null
                : MiscTools.getSelfTerm(innermostMethodFrame, services);

        final ExecutionContext innermostExecutionContext = //
                innermostMethodFrame == null ? null
                        : (ExecutionContext) innermostMethodFrame
                                .getExecutionContext();
        services.getSpecificationRepository().addLoopInvariant(spec);

        // cache and return result
        final Instantiation result = new Instantiation( //
                u, progPost, loop, spec, selfTerm, innermostExecutionContext);

        lastFocusTerm = focusTerm;
        lastInstantiation = result;

        return result;
    }

    /**
     * TODO
     * 
     * @param tb
     * @param term
     * @return
     */
    private static Term and(TermBuilder tb, Term t1, Term t2) {
        assert t2 != null;
        return t1 == null ? t2 : tb.and(t1, t2);
    }

    // -------------------------------------------------------------------------
    // helper methods for apply()
    // -------------------------------------------------------------------------

    /**
     * TODO
     * 
     * @param services
     * @param inst
     * @param atPres
     * @param heapContext
     * @return
     */
    private Term conjunctInv(Services services, Instantiation inst,
            final Map<LocationVariable, Term> atPres,
            final List<LocationVariable> heapContext) {
        return mapAndConjunct(services, (pv -> inst.inv.getInvariant(pv,
                inst.selfTerm, atPres, services)), heapContext);
    }

    /**
     * TODO
     * 
     * @param services
     * @param inst
     * @param atPres
     * @param heapContext
     * @return
     */
    private Term conjunctFreeInv(Services services, Instantiation inst,
            final Map<LocationVariable, Term> atPres,
            final List<LocationVariable> heapContext) {
        return mapAndConjunct(services, (pv -> inst.inv.getFreeInvariant(pv,
                inst.selfTerm, atPres, services)), heapContext);
    }

    /**
     * TODO
     * 
     * @param services
     * @param inst
     * @param atPres
     * @param listOfT
     * @return
     */
    private <T> Term mapAndConjunct(Services services,
            java.util.function.Function<T, Term> fct, final List<T> listOfT) {
        final TermBuilder tb = services.getTermBuilder();

        //@formatter:off
        return listOfT.stream()
                .map(t -> fct.apply(t))
                .filter(term -> term != null)
                .reduce(tb.tt(), (acc, term) -> tb.and(acc, term));
        //@formatter:on
    }

    /**
     * TODO
     * 
     * @param inst
     * @param variant
     * @param services
     * @return
     */
    private Pair<Term, Term> prepareVariant(Instantiation inst, Term variant,
            TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final ProgramElementName variantName = new ProgramElementName(
                tb.newName("variant"));
        final LocationVariable variantPV = new LocationVariable(variantName,
                Sort.ANY);
        services.getNamespaces().programVariables().addSafely(variantPV);

        final boolean dia = ((Modality) inst.progPost.op())
                .terminationSensitive();
        final Term variantUpdate = dia ? tb.elementary(variantPV, variant)
                : tb.skip();
        final Term variantPO = dia ? tb.prec(variant, tb.var(variantPV))
                : tb.tt();
        return new Pair<Term, Term>(variantUpdate, variantPO);
    }

    /**
     * TODO
     * 
     * @param termLabelState
     * @param inst
     * @param invTerm
     * @param reachableState
     * @param services
     * @param initGoal
     * @return
     */
    private SequentFormula initFormula(TermLabelState termLabelState,
            Instantiation inst, final Term invTerm, Term reachableState,
            Services services, Goal initGoal) {
        final TermBuilder tb = services.getTermBuilder();

        Term sfTerm = tb.apply(inst.u, tb.and(invTerm, reachableState), null);
        sfTerm = TermLabelManager.refactorTerm(termLabelState, services, null,
                sfTerm, this, initGoal, INITIAL_INVARIANT_ONLY_HINT, null);

        return new SequentFormula(sfTerm);
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    /**
     * TODO
     */
    private static final class Instantiation {
        public final Term u;
        public final Term progPost;
        public final While loop;
        public final LoopSpecification inv;
        public final Term selfTerm;
        // TODO Removed this field; was however used in old invariant rule.
        // Might be needed for IF or well-definedness or whatever...
        public final ExecutionContext innermostExecutionContext;

        public Instantiation(Term u, Term progPost, While loop,
                LoopSpecification inv, Term selfTerm,
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

    /**
     * TODO
     *
     * @author Dominic Scheurer
     */
    private static class AnonUpdateData {
        public final Term anonUpdate, anonHeap;
        // TODO Removed these fields; were however used in old invariant rule.
        // Might be needed for IF or well-definedness or whatever...
        // public final Term loopHeap, loopHeapAtPre;

        public AnonUpdateData(Term anonUpdate, Term loopHeap,
                Term loopHeapAtPre, Term anonHeap) {
            this.anonUpdate = anonUpdate;
            // this.loopHeap = loopHeap;
            // this.loopHeapAtPre = loopHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }

}
