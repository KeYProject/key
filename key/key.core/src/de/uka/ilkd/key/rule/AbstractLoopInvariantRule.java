package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * An abstract super class for loop invariant rules.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractLoopInvariantRule implements BuiltInRule {

    /**
     * The last formula the loop invariant rule was applied to. Used for
     * checking whether {@link #lastInstantiation} can be used instead of doing
     * a new instantiation.
     */
    private static Term lastFocusTerm;

    /**
     * A simple cache which ensures that we don't instantiate the rule multiple
     * times for the same loop.
     */
    private static Instantiation lastInstantiation;

    public AbstractLoopInvariantRule() {
        super();
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

    @Override
    public String displayName() {
        return name().toString();
    }

    @Override
    public String toString() {
        return displayName();
    }

    /**
     * Creates the "...Before_LOOP" update needed for the variant.
     * 
     * @param services
     *            The {@link Services} object.
     * @param heapContext
     *            TODO
     * @param localOuts
     *            TODO
     * @param heapToBeforeLoop
     *            TODO
     * @return The "...Before_LOOP" update needed for the variant.
     */
    protected static Term createBeforeLoopUpdate(Services services,
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
     * Creates an update for the anonymization of all {@link ProgramVariable}s
     * in localOuts.
     * 
     * @param localOuts
     *            The {@link ProgramVariable}s to anonymize.
     * @param services
     *            The {@link Services} object.
     * @return The anonymizing update.
     */
    protected static Term createLocalAnonUpdate(
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
     * Creates a conjunction of all invariant formulas for the
     * {@link LocationVariable}s in heapContext.
     * 
     * @param services
     *            The {@link Services} object.
     * @param inst
     *            The {@link Instantiation} for this rule application.
     * @param atPres
     *            TODO
     * @param heapContext
     *            The heap formulas to create a conjunction of invariants for.
     * @return A conjunction of all invariant formulas for the
     *         {@link LocationVariable}s in heapContext.
     */
    protected Term conjunctInv(Services services, Instantiation inst,
            final Map<LocationVariable, Term> atPres,
            final List<LocationVariable> heapContext) {
        return mapAndConjunct(services, (pv -> inst.inv.getInvariant(pv,
                inst.selfTerm, atPres, services)), heapContext);
    }

    /**
     * Creates a conjunction of all <em>free</em> invariant formulas for the
     * {@link LocationVariable}s in heapContext.
     * 
     * @param services
     *            The {@link Services} object.
     * @param inst
     *            The {@link Instantiation} for this rule application.
     * @param atPres
     *            TODO
     * @param heapContext
     *            The heap formulas to create a conjunction of <em>free</em>
     *            invariants for.
     * @return A conjunction of all <em>free</em> invariant formulas for the
     *         {@link LocationVariable}s in heapContext.
     */
    protected Term conjunctFreeInv(Services services, Instantiation inst,
            final Map<LocationVariable, Term> atPres,
            final List<LocationVariable> heapContext) {
        return mapAndConjunct(services, (pv -> inst.inv.getFreeInvariant(pv,
                inst.selfTerm, atPres, services)), heapContext);
    }

    /**
     * Creates a conjunction of {@link Term}s that are produced by fct from the
     * elements in listOfT. fct may return null when applied to a T object; in
     * this case, the result is ignored when constructing the conjunction.
     * 
     * @param services
     *            The {@link Services} object.
     * @param fct
     *            A mapping from T objects to {@link Term}s (formulas!).
     * @param listOfT
     *            A list of T objects.
     * @return A conjunction of Terms produced by fct for all elements in
     *         listOfT.
     */
    protected <T> Term mapAndConjunct(Services services,
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
     * Creates the variant proof obligation and update.
     * 
     * @param inst
     *            The {@link Instantiation} for this rule application.
     * @param variant
     *            The variant term as given by the loop specification.
     * @param services
     *            The {@link Services} object.
     * @return The variant proof obligation and update.
     */
    protected Pair<Term, Term> prepareVariant(Instantiation inst, Term variant,
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
     * Splits a term into the update and formula part.
     * 
     * @param focusTerm
     *            The term to split into update and formula the update is
     *            applied to.
     * @param services
     *            The {@link Services} object.
     * @return A pair of the update and the formula the update is applied to.
     */
    protected static Pair<Term, Term> splitUpdates(Term focusTerm,
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
     * Checks whether progPost contains a Java program.
     * 
     * @param progPost
     *            The Term to check.
     * @return true iff progPost (directly) contains a Java program.
     */
    protected static boolean isModalityTerm(final Term progPost) {
        // focus (below update) must be modality term
        // TODO isn't that the same as !progPost.javaBlock().isEmpty() ?
        return progPost.op() instanceof Modality;
    }

    /**
     * Creates a conjunction of t1 and t2 if both are not null, and returns t2
     * only if t1 is null.
     * 
     * @param tb
     *            The {@link TermBuilder} object.
     * @param t1
     *            The first formula of the conjunction; may be null.
     * @param t2
     *            The second formula of the conjunction; may <em>not</em> be
     *            null.
     * @return Returns t2 if t1 is null and t1 & t2 if both aren't null.
     */
    protected static Term and(TermBuilder tb, Term t1, Term t2) {
        assert t2 != null;
        return t1 == null ? t2 : tb.and(t1, t2);
    }

    /**
     * Constructs the {@link Instantiation} object containing the relevant
     * parameters for this {@link LoopScopeInvariantRule} application.
     * 
     * @param app
     *            The {@link LoopInvariantBuiltInRuleApp} object for the
     *            application of the {@link LoopScopeInvariantRule}.
     * @param services
     *            The {@link Services} object.
     * @return The {@link Instantiation} object containing the relevant
     *         parameters for this {@link LoopScopeInvariantRule} application.
     * @throws RuleAbortException
     *             If the {@link LoopInvariantBuiltInRuleApp} does not contain a
     *             {@link LoopSpecification}.
     */
    protected static Instantiation instantiate(
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
     * Computes the anonymizing update, the loop heap, the base heap, and the
     * anonymized heap.
     * 
     * @param heap
     *            The original heap {@link LocationVariable}.
     * @param mod
     *            The modifiers term.
     * @param inv
     *            The loop invariant.
     * @param services
     *            The {@link Services} object.
     * @return An {@link AnonUpdateData} object encapsulating the anonymizing
     *         update, the loop heap, the base heap, and the anonymized heap.
     */
    protected static AnonUpdateData createAnonUpdate(LocationVariable heap,
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

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    /**
     * A container for an instantiation of this {@link LoopScopeInvariantRule}
     * application; contains the update, the program with post condition, the
     * {@link While} loop the {@link LoopScopeInvariantRule} should be applied
     * to, the {@link LoopSpecification}, the the self {@link Term}.
     */
    protected static final class Instantiation {
        public final Term u;
        public final Term progPost;
        public final While loop;
        public final LoopSpecification inv;
        public final Term selfTerm;
        // TODO Removed this field; was however used in old invariant rule.
        // Could be needed for the information flow validity goal.
        // public final ExecutionContext innermostExecutionContext;

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
            // this.innermostExecutionContext = innermostExecutionContext;
        }
    }

    /**
     * A container containing data for the anonymizing update, that is the
     * actual update and the anonymized heap.
     */
    protected static class AnonUpdateData {
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