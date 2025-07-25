/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * An abstract super class for loop invariant rules. Extending rules should usually call
 * {@link #doPreparations(Goal, RuleApp)} directly at the beginning of
 * the {@link BuiltInRule#apply(Goal, RuleApp)} method.
 *
 * @see LoopScopeInvariantRule
 * @see WhileInvariantRule
 * @author Dominic Scheurer
 */
public abstract class AbstractLoopInvariantRule implements BuiltInRule {

    /**
     * The last formula the loop invariant rule was applied to. Used for checking whether
     * {@link #lastInstantiation} can be used instead of doing a new instantiation.
     */
    private static JTerm lastFocusTerm;

    /**
     * A simple cache which ensures that we don't instantiate the rule multiple times for the same
     * loop.
     */
    private static Instantiation lastInstantiation;

    /**
     * @return The number of generated goals by this invariant rule.
     */
    public abstract int getNrOfGoals();

    /**
     * Constructs the data needed for the currently implemented loop invariants; also prepares the
     * new set of goals, that is splitting the current goal is no longer required after calling this
     * method.
     *
     * @param goal the Goal on which to apply <tt>ruleApp</tt>
     * @param ruleApp the rule application to be executed
     * @return The {@link LoopInvariantInformation} object containing the data for the application
     *         of loop invariant rules.
     */
    public LoopInvariantInformation doPreparations(Goal goal,
            RuleApp ruleApp)
            throws RuleAbortException {
        final var services = goal.getOverlayServices();
        // Basic objects needed for rule application
        final TermBuilder tb = services.getTermBuilder();
        final TermLabelState termLabelState = new TermLabelState();
        final LoopInvariantBuiltInRuleApp loopRuleApp = (LoopInvariantBuiltInRuleApp) ruleApp;

        // Get the Instantiation object
        final Instantiation inst = instantiate(loopRuleApp, services);

        // Get necessary parts of invariant and sequent
        final Map<LocationVariable, JTerm> atPres = inst.inv.getInternalAtPres();
        final List<LocationVariable> heapContext = ((IBuiltInRuleApp) ruleApp).getHeapContext();

        final JTerm invTerm = conjunctInv(services, inst, atPres, heapContext);
        final JTerm invFreeTerm = conjunctFreeInv(services, inst, atPres, heapContext);

        // Collect input and output local variables,
        // prepare reachableOut.
        // TODO: reachableIn has been removed since it was not even used in the
        // old invariant rule. Is that OK or was there an earlier mistake?
        final ImmutableSet<LocationVariable> localOuts =
            MiscTools.getLocalOuts(inst.loop, services);

        final Map<LocationVariable, Map<JTerm, JTerm>> heapToBeforeLoop = //
            new LinkedHashMap<>();

        // Create update for values before loop
        JTerm beforeLoopUpdate =
            createBeforeLoopUpdate(services, heapContext, localOuts, heapToBeforeLoop);

        // prepare anon update, frame condition, etc.
        AdditionalHeapTerms additionalHeapTerms = createAdditionalHeapTerms(services, inst,
            heapContext, localOuts, heapToBeforeLoop, atPres);

        // Prepare variant
        final JTerm variant = //
            inst.inv.getVariant(inst.selfTerm, atPres, services);
        final Pair<JTerm, JTerm> variantUpdAndPO = prepareVariant(inst, variant, services);
        final JTerm variantUpdate = variantUpdAndPO.first;
        final JTerm variantPO = variantUpdAndPO.second;

        // Prepare common assumption
        final JTerm reachableOut = localOuts.stream().map(tb::reachableValue)
                .reduce(tb.tt(), tb::and);

        final JTerm[] uAnon = { inst.u, additionalHeapTerms.anonUpdate };
        final JTerm[] uBeforeLoopDefAnonVariant =
            { inst.u, beforeLoopUpdate, additionalHeapTerms.anonUpdate, variantUpdate };
        final JTerm uAnonInv =
            tb.applySequential(uAnon, tb.and(tb.and(invTerm, reachableOut), invFreeTerm));

        // Prepare the new goals
        ImmutableList<Goal> goals = goal.split(getNrOfGoals());

        return new LoopInvariantInformation(goal, services, inst, loopRuleApp, goals,
            termLabelState, invTerm, variantPO, additionalHeapTerms.reachableState,
            additionalHeapTerms.anonUpdate, additionalHeapTerms.wellFormedAnon, uAnonInv,
            additionalHeapTerms.frameCondition, uBeforeLoopDefAnonVariant,
            additionalHeapTerms.anonUpdateData);
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec() || Transformer.inTransformer(pio)) {
            return false;
        }

        final JTerm progPost =
            splitUpdates((JTerm) pio.subTerm(), goal.proof().getServices()).second;
        JavaBlock javaBlock = progPost.javaBlock();

        return !javaBlock.isEmpty() && JavaTools.getActiveStatement(javaBlock) instanceof While;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
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
     * @param services The {@link Services} object.
     * @param heapContext TODO
     * @param localOuts TODO
     * @param heapToBeforeLoop TODO
     * @return The "...Before_LOOP" update needed for the variant.
     */
    protected static JTerm createBeforeLoopUpdate(Services services,
            final List<LocationVariable> heapContext,
            final ImmutableSet<LocationVariable> localOuts,
            final Map<LocationVariable, Map<JTerm, JTerm>> heapToBeforeLoop) {
        final TermBuilder tb = services.getTermBuilder();
        final Namespace<IProgramVariable> progVarNS = services.getNamespaces().programVariables();

        JTerm beforeLoopUpdate = null;
        for (LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<>());
            final LocationVariable lv =
                tb.locationVariable(heap + "Before_LOOP", heap.sort(), true);
            progVarNS.addSafely(lv);

            final JTerm u = tb.elementary(lv, tb.var(heap));
            if (beforeLoopUpdate == null) {
                beforeLoopUpdate = u;
            } else {
                beforeLoopUpdate = tb.parallel(beforeLoopUpdate, u);
            }

            heapToBeforeLoop.get(heap).put(tb.var(heap), tb.var(lv));
        }

        for (ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName = tb.newName(pv.name() + "Before_LOOP");
            final LocationVariable pvBeforeLoop =
                new LocationVariable(new ProgramElementName(pvBeforeLoopName), pv.getKeYJavaType());
            progVarNS.addSafely(pvBeforeLoop);
            beforeLoopUpdate =
                tb.parallel(beforeLoopUpdate, tb.elementary(pvBeforeLoop, tb.var(pv)));
            heapToBeforeLoop.get(services.getTypeConverter().getHeapLDT().getHeap()).put(tb.var(pv),
                tb.var(pvBeforeLoop));
        }

        return beforeLoopUpdate;
    }

    /**
     * Creates an update for the anonymization of all {@link ProgramVariable}s in localOuts.
     *
     * @param localOuts The {@link ProgramVariable}s to anonymize.
     * @param services The {@link Services} object.
     * @return The anonymizing update.
     */
    protected static JTerm createLocalAnonUpdate(ImmutableSet<LocationVariable> localOuts,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        return localOuts.stream().map(pv -> {
            final Function anonFunc =
                new JFunction(new Name(tb.newName(pv.name().toString())), pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);

            return tb.elementary(pv, tb.func(anonFunc));
        }).reduce(tb.skip(), tb::parallel);
    }

    /**
     * Creates a conjunction of all invariant formulas for the {@link LocationVariable}s in
     * heapContext.
     *
     * @param services The {@link Services} object.
     * @param inst The {@link Instantiation} for this rule application.
     * @param atPres TODO
     * @param heapContext The heap formulas to create a conjunction of invariants for.
     * @return A conjunction of all invariant formulas for the {@link LocationVariable}s in
     *         heapContext.
     */
    protected static JTerm conjunctInv(Services services, Instantiation inst,
            final Map<LocationVariable, JTerm> atPres, final List<LocationVariable> heapContext) {
        return mapAndConjunct(services,
            (pv -> inst.inv.getInvariant(pv, inst.selfTerm, atPres, services)), heapContext);
    }

    /**
     * Creates a conjunction of all <em>free</em> invariant formulas for the
     * {@link LocationVariable}s in heapContext.
     *
     * @param services The {@link Services} object.
     * @param inst The {@link Instantiation} for this rule application.
     * @param atPres TODO
     * @param heapContext The heap formulas to create a conjunction of <em>free</em> invariants for.
     * @return A conjunction of all <em>free</em> invariant formulas for the
     *         {@link LocationVariable}s in heapContext.
     */
    protected static JTerm conjunctFreeInv(Services services, Instantiation inst,
            final Map<LocationVariable, JTerm> atPres, final List<LocationVariable> heapContext) {
        return mapAndConjunct(services,
            (pv -> inst.inv.getFreeInvariant(pv, inst.selfTerm, atPres, services)), heapContext);
    }

    /**
     * Creates a conjunction of {@link JTerm}s that are produced by fct from the elements in
     * listOfT.
     * fct may return null when applied to a T object; in this case, the result is ignored when
     * constructing the conjunction.
     *
     * @param services The {@link Services} object.
     * @param fct A mapping from T objects to {@link JTerm}s (formulas!).
     * @param listOfT A list of T objects.
     * @return A conjunction of Terms produced by fct for all elements in listOfT.
     */
    protected static <T> JTerm mapAndConjunct(Services services,
            java.util.function.Function<T, JTerm> fct, final List<T> listOfT) {
        final TermBuilder tb = services.getTermBuilder();

        //@formatter:off
        return listOfT.stream()
                .map(fct)
                .filter(Objects::nonNull)
                .reduce(tb.tt(), tb::and);
        //@formatter:on
    }

    /**
     * Creates the variant proof obligation and update.
     *
     * @param inst The {@link Instantiation} for this rule application.
     * @param variant The variant term as given by the loop specification.
     * @param services The {@link Services} object.
     * @return The variant proof obligation and update.
     */
    protected static Pair<JTerm, JTerm> prepareVariant(Instantiation inst, JTerm variant,
            TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final ProgramElementName variantName = new ProgramElementName(tb.newName("variant"));
        final LocationVariable variantPV = new LocationVariable(variantName, JavaDLTheory.ANY);
        services.getNamespaces().programVariables().addSafely(variantPV);

        JModality modality = ((JModality) inst.progPost.op());
        final boolean dia = modality.<JModality.JavaModalityKind>kind().terminationSensitive();
        final JTerm variantUpdate = dia ? tb.elementary(variantPV, variant) : tb.skip();
        final JTerm variantPO = dia ? tb.prec(variant, tb.var(variantPV)) : tb.tt();

        return new Pair<>(variantUpdate, variantPO);
    }

    /**
     * Splits a term into the update and formula part.
     *
     * @param focusTerm The term to split into update and formula the update is applied to.
     * @param services The {@link Services} object.
     * @return A pair of the update and the formula the update is applied to.
     */
    protected static Pair<JTerm, JTerm> splitUpdates(JTerm focusTerm, TermServices services) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<>(UpdateApplication.getUpdate(focusTerm),
                UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<>(services.getTermBuilder().skip(), focusTerm);
        }
    }

    /**
     * Checks whether progPost contains a Java program.
     *
     * @param progPost The Term to check.
     * @return true iff progPost (directly) contains a Java program.
     */
    protected static boolean isModalityTerm(final JTerm progPost) {
        // focus (below update) must be modality term
        // TODO isn't that the same as !progPost.javaBlock().isEmpty() ?
        return progPost.op() instanceof JModality;
    }

    /**
     * Creates a conjunction of t1 and t2 if both are not null, and returns t2 only if t1 is null.
     *
     * @param tb The {@link TermBuilder} object.
     * @param t1 The first formula of the conjunction; may be null.
     * @param t2 The second formula of the conjunction; may <em>not</em> be null.
     * @return returns {@code t2} if {@code t1} is null and {@code t1 & t2} if both aren't null.
     */
    protected static JTerm and(TermBuilder tb, JTerm t1, JTerm t2) {
        assert t2 != null;
        return t1 == null ? t2 : tb.and(t1, t2);
    }

    /**
     * Constructs the {@link Instantiation} object containing the relevant parameters for this
     * {@link LoopScopeInvariantRule} application.
     *
     * @param app The {@link LoopInvariantBuiltInRuleApp} object for the application of the
     *        {@link LoopScopeInvariantRule}.
     * @param services The {@link Services} object.
     * @return The {@link Instantiation} object containing the relevant parameters for this
     *         {@link LoopScopeInvariantRule} application.
     * @throws RuleAbortException If the {@link LoopInvariantBuiltInRuleApp} does not contain a
     *         {@link LoopSpecification}.
     */
    protected static Instantiation instantiate(final LoopInvariantBuiltInRuleApp app,
            Services services) throws RuleAbortException {
        final JTerm focusTerm = (JTerm) app.posInOccurrence().subTerm();

        if (focusTerm == lastFocusTerm && lastInstantiation.inv == services
                .getSpecificationRepository().getLoopSpec(lastInstantiation.loop)) {
            return lastInstantiation;
        }

        // leading update?
        final Pair<JTerm, JTerm> update = splitUpdates(focusTerm, services);
        final JTerm u = update.first;
        final JTerm progPost = update.second;

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
        final MethodFrame innermostMethodFrame =
            JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
        if (innermostMethodFrame != null) {
            spec = spec.setTarget(innermostMethodFrame.getProgramMethod());
        }

        final JTerm selfTerm = innermostMethodFrame == null ? null
                : MiscTools.getSelfTerm(innermostMethodFrame, services);

        final ExecutionContext innermostExecutionContext = //
            innermostMethodFrame == null ? null
                    : (ExecutionContext) innermostMethodFrame.getExecutionContext();
        services.getSpecificationRepository().addLoopInvariant(spec);

        // cache and return result
        final Instantiation result = new Instantiation( //
            u, progPost, loop, spec, selfTerm, innermostExecutionContext);

        lastFocusTerm = focusTerm;
        lastInstantiation = result;

        return result;
    }

    /**
     * Computes the anonymizing update, the loop heap, the base heap, and the anonymized heap.
     *
     * @param heap The original heap {@link LocationVariable}.
     * @param modifiable The modifiable term.
     * @param inv The loop invariant.
     * @param services The {@link Services} object.
     * @return An {@link AnonUpdateData} object encapsulating the anonymizing update, the loop heap,
     *         the base heap, and the anonymized heap.
     */
    protected static AnonUpdateData createAnonUpdate(LocationVariable heap, JTerm modifiable,
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

        return new AnonUpdateData( //
            anonUpdate, loopHeap, //
            tb.getBaseHeap(), anonHeapTerm);
    }

    /**
     * Prepare anon update, wellformed formula, frame condition and reachable state formula.
     *
     * @param services The {@link Services} object.
     * @param inst The {@link Instantiation} of parameters for the {@link LoopScopeInvariantRule}
     *        app.
     * @param heapContext TODO
     * @param localOuts TODO
     * @param heapToBeforeLoop TODO
     * @param atPres TODO
     * @return An {@link AdditionalHeapTerms} object containing the anonymized update, the
     *         wellformed formula, the frame condition formula, and the reachable state formula.
     */
    protected static AdditionalHeapTerms createAdditionalHeapTerms(Services services,
            final Instantiation inst, final List<LocationVariable> heapContext,
            final ImmutableSet<LocationVariable> localOuts,
            final Map<LocationVariable, Map<JTerm, JTerm>> heapToBeforeLoop,
            Map<LocationVariable, JTerm> atPres) {
        final TermBuilder tb = services.getTermBuilder();

        JTerm anonUpdate = createLocalAnonUpdate(localOuts, services);
        // can still be null
        if (anonUpdate == null) {
            anonUpdate = tb.skip();
        }

        JTerm wellFormedAnon = null;
        JTerm frameCondition = null;
        JTerm reachableState = null;

        final Map<LocationVariable, JTerm> modifiables = new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> freeModifiables = new LinkedHashMap<>();
        for (LocationVariable heap : heapContext) {
            modifiables.put(heap, inst.inv.getModifiable(heap, inst.selfTerm, atPres, services));
            freeModifiables.put(heap,
                inst.inv.getFreeModifiable(heap, inst.selfTerm, atPres, services));
        }

        ImmutableList<AnonUpdateData> anonUpdateData = ImmutableSLList.nil();
        for (LocationVariable heap : heapContext) {
            // weigl: prevent NPE
            JTerm modifiableTerm = modifiables.get(heap);
            modifiableTerm = modifiableTerm == null ? tb.strictlyNothing() : modifiableTerm;
            final AnonUpdateData tAnon = createAnonUpdate(heap, modifiableTerm, inst.inv, services);
            anonUpdateData = anonUpdateData.append(tAnon);

            anonUpdate = tb.parallel(anonUpdate, tAnon.anonUpdate);

            wellFormedAnon = and(tb, wellFormedAnon, tb.wellFormed(tAnon.anonHeap));

            final JTerm modifiable = modifiables.get(heap);
            final JTerm freeModifiable = freeModifiables.get(heap);
            final JTerm strictlyNothing = tb.strictlyNothing();
            final JTerm currentFrame;
            if (strictlyNothing.equalsModProperty(modifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                if (strictlyNothing.equalsModProperty(freeModifiable,
                    IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    currentFrame = tb.frameStrictlyEmpty(tb.var(heap), heapToBeforeLoop.get(heap));
                } else {
                    currentFrame =
                        tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), freeModifiable);
                }
            } else {
                if (strictlyNothing.equalsModProperty(freeModifiable,
                    IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    currentFrame = tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), modifiable);
                } else {
                    currentFrame = tb.frame(
                        tb.var(heap), heapToBeforeLoop.get(heap),
                        tb.union(modifiable, freeModifiable));
                }
            }

            frameCondition = and(tb, frameCondition, currentFrame);
            reachableState = and(tb, reachableState, tb.wellFormed(heap));
        }

        return new AdditionalHeapTerms(anonUpdate, wellFormedAnon, frameCondition, reachableState,
            anonUpdateData);
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    /**
     * A container with data for the additional terms with assertions about the heap; that is, the
     * anonymizing update, the wellformed term, the frame condition and the reachable state formula.
     *
     * @author Dominic Scheurer
     */
    protected record AdditionalHeapTerms(JTerm anonUpdate, JTerm wellFormedAnon,
            JTerm frameCondition,
            JTerm reachableState,
            ImmutableList<AnonUpdateData> anonUpdateData) {
    }

    /**
     * A container for an instantiation of this {@link LoopScopeInvariantRule} application; contains
     * the update, the program with post condition, the {@link While} loop the
     * {@link LoopScopeInvariantRule} should be applied to, the {@link LoopSpecification}, the
     * self {@link JTerm}.
     *
     * @param innermostExecutionContext TODO Removed this field; was however used in old invariant
     *        rule. Could be needed for the information flow validity goal.
     */
    public record Instantiation(JTerm u, JTerm progPost, While loop, LoopSpecification inv,
            JTerm selfTerm,
            ExecutionContext innermostExecutionContext) {
        public Instantiation {
            assert u != null;
            assert u.sort() == JavaDLTheory.UPDATE;
            assert progPost != null;
            assert progPost.sort() == JavaDLTheory.FORMULA;
            assert loop != null;
            assert inv != null;

        }
    }

    /**
     * A container containing data for the anonymizing update, that is the actual update and the
     * anonymized heap.
     */
    protected static class AnonUpdateData {
        public final JTerm anonUpdate, anonHeap, loopHeap, loopHeapAtPre;

        public AnonUpdateData(JTerm anonUpdate, JTerm loopHeap, JTerm loopHeapAtPre,
                JTerm anonHeap) {
            this.anonUpdate = anonUpdate;
            this.loopHeap = loopHeap;
            this.loopHeapAtPre = loopHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }

    /**
     * A container object containing the information required for the concrete loop invariant rules
     * to create the sequents for the new goals.
     *
     * @param goal The original goal.
     * @param services The {@link Services} object.
     * @param inst The {@link Instantiation} of parameters for the {@link LoopScopeInvariantRule}
     *        app.
     * @param ruleApp The {@link RuleApp} for this {@link LoopScopeInvariantRule} application.
     * @param goals The goals created by the invariant rules application; those are filled with
     *        content by
     *        the concrete loop invariant rules.
     * @param termLabelState The {@link TermLabelState}.
     * @param invTerm The loop invariant formula.
     * @param variantPO The proof obligation for the variant.
     * @param reachableState The reachable state formula.
     * @param anonUpdate The anonymized update {@link JTerm}.
     * @param wellFormedAnon The wellformed formula.
     * @param uAnonInv A formula containing the anonymized update and the loop invariant.
     * @param frameCondition The frame condition.
     * @param uBeforeLoopDefAnonVariant An array containing the original update, the "before the
     *        loop" update for reasoning about
     *        the variant, the anonymized update, and the variant update.
     * @param anonUpdateData Anonymizing updates for all heaps.
     */
    public record LoopInvariantInformation(Goal goal, Services services, Instantiation inst,
            LoopInvariantBuiltInRuleApp ruleApp, ImmutableList<Goal> goals,
            TermLabelState termLabelState, JTerm invTerm, JTerm variantPO,
            JTerm reachableState, JTerm anonUpdate, JTerm wellFormedAnon, JTerm uAnonInv,
            JTerm frameCondition, JTerm[] uBeforeLoopDefAnonVariant,
            ImmutableList<AnonUpdateData> anonUpdateData) {
        /**
         * Creates a new {@link LoopInvariantInformation} object.
         *
         * @param goal TODO
         * @param services The {@link Services} object.
         * @param inst The {@link Instantiation} of parameters for the
         *        {@link LoopScopeInvariantRule} app.
         * @param ruleApp The {@link RuleApp} for this {@link LoopScopeInvariantRule} application.
         * @param goals The goals created by the invariant rules application; those are filled with
         *        content by the concrete loop invariant rules.
         * @param termLabelState The {@link TermLabelState}.
         * @param invTerm The loop invariant formula.
         * @param variantPO The proof obligation for the variant.
         * @param reachableState The reachable state formula.
         * @param anonUpdate The anonymized update {@link JTerm}.
         * @param wellFormedAnon The wellformed formula.
         * @param uAnonInv A formula containing the anonymized update and the loop invariant.
         * @param frameCondition The frame condition.
         * @param uBeforeLoopDefAnonVariant An array containing the original update, the "before the
         *        loop" update for reasoning about the variant, the anonymized update, and the
         *        variant update.
         * @param anonUpdateData TODO
         */
        public LoopInvariantInformation {
        }
    }

}
