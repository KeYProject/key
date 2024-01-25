/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.TacletIndexKit;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Immutables;

import org.jspecify.annotations.NonNull;


public final class OneStepSimplifier implements BuiltInRule {

    /**
     * If true, the OneStepSimplifier has access to the entire sequent during replay.
     * If false, it is restricted to the formulas specified in the proof file.
     *
     * Only activate when loading old proof files (that do not contain this information)!
     *
     * @see #apply(Goal, Services, RuleApp)
     */
    public static boolean disableOSSRestriction = false;
    /**
     * If true, the simplification process will stop on cycles.
     * Note that cycles should never happen by careful selection of the rulesets.
     */
    private static final boolean ENABLE_CYCLE_CHECK = true;
    /**
     * If true, the simplifier will keep a log of rule applications.
     * This may lead to excessive memory consumption, so it can be disabled here.
     * TODO: add a real (user-facing) option?
     */
    private static final boolean ENABLE_PROTOCOL = true;

    private static final int APPLICABILITY_CACHE_SIZE = 1000;
    private static final int DEFAULT_CACHE_SIZE = 10000;

    /**
     * Represents a list of rule applications performed in one OSS step.
     */
    public static final class Protocol extends ArrayList<RuleApp> {
        private static final long serialVersionUID = 8788009073806993077L;
    }

    private static final Name NAME = new Name("One Step Simplification");

    /**
     * Rule sets to capture. Automated performance tests showed that including more rule sets here
     * would not improve prover performance. I tested it for "simplify_literals", "cast_del", and
     * "evaluate_instanceof"; in any case there was a measurable slowdown. -- DB 03/06/14
     */
    private static final ImmutableList<String> ruleSets = ImmutableSLList.<String>nil()
            .append("concrete").append("update_elim").append("update_apply_on_update")
            .append("update_apply").append("update_join").append("elimQuantifier");

    private static final boolean[] bottomUp = { false, false, true, true, true, false };
    private final Map<SequentFormula, Boolean> applicabilityCache =
        new LRUCache<>(APPLICABILITY_CACHE_SIZE);
    /**
     * Whether the OSS rule is currently checked for applicability.
     * This means that it is only necessary to prove that one single rule app is possible.
     */
    private boolean applicableCheck = false;

    private Proof lastProof;
    private ImmutableList<NoPosTacletApp> appsTakenOver;
    private TacletIndex[] indices;
    private Map<Term, Term>[] notSimplifiableCaches;
    private boolean active;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public OneStepSimplifier() { // Visibility must be public because it is no longer a singleton in
                                 // general. Side proofs use own OneStepSimplifier instances for
                                 // parallelization. This is required thanks to the internal state
                                 // of this rule.
        assert bottomUp.length == ruleSets.size();
    }



    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Selects the taclets suitable for one step simplification out of the given rule set (where
     * taclets that also belong to one of the "excluded" rule sets are not considered). Removes
     * these taclets from the goal's taclet index, remembers them in the "appsTakenOver" field so
     * they can be restored later, and returns them.
     */
    private ImmutableList<Taclet> tacletsForRuleSet(Proof proof, String ruleSetName,
            ImmutableList<String> excludedRuleSetNames) {
        assert !proof.openGoals().isEmpty();
        ImmutableList<Taclet> result = ImmutableSLList.nil();

        // collect apps present in all open goals
        Set<NoPosTacletApp> allApps =
            proof.openGoals().head().ruleAppIndex().tacletIndex().allNoPosTacletApps();
        for (Goal goal : proof.openGoals().tail()) {
            allApps.retainAll(goal.ruleAppIndex().tacletIndex().allNoPosTacletApps());
        }

        // identify those apps suitable for the one step simplifier;
        // store them in appsTakenOver and their taclets in result
        for (NoPosTacletApp app : allApps) {
            final Taclet tac = app.taclet();
            if (!(tac instanceof RewriteTaclet) || !tac.hasReplaceWith()
                    || !tac.ifSequent().isEmpty() || tac.goalTemplates().size() != 1
                    || !tac.goalTemplates().head().sequent().isEmpty() || !tac.varsNew().isEmpty()
                    || !tac.varsNewDependingOn().isEmpty()
                    || ((RewriteTaclet) tac).getApplicationRestriction() != RewriteTaclet.NONE
                    || !proof.getInitConfig().getJustifInfo().getJustification(tac)
                            .isAxiomJustification()) {
                continue;
            }

            boolean accept = false;
            for (RuleSet rs : app.taclet().getRuleSets()) {
                if (rs.name().toString().equals(ruleSetName)) {
                    accept = true;
                } else if (excludedRuleSetNames.contains(rs.name().toString())) {
                    accept = false;
                    break;
                }
            }

            if (accept) {
                appsTakenOver = appsTakenOver.prepend(app);
                result = result.prepend(tac);
            }
        }

        // Inefficient immutable sets replaced by immutable lists.
        // Make sure that semantics are the same:
        // (Checks are pretty expensive O(n); could be removed after some time)
        // MU May 2016

        assert Immutables.isDuplicateFree(appsTakenOver)
                : "If this fails unexpectedly, add a call to Immutables.removeDuplicates.";
        assert Immutables.isDuplicateFree(result)
                : "If this fails unexpectedly, add a call to Immutables.removeDuplicates.";

        // remove apps in appsTakenOver from taclet indices of all goals
        for (NoPosTacletApp app : appsTakenOver) {
            for (Goal goal : proof.allGoals()) {
                goal.ruleAppIndex().removeNoPosTacletApp(app);
            }
        }

        return result;
    }


    /**
     * If the rule is applied to a different proof than last time, then clear all caches and
     * initialise the taclet indices.
     */
    @SuppressWarnings("unchecked")
    private void initIndices(Proof proof) {
        if (proof != lastProof) {
            shutdownIndices();
            lastProof = proof;
            appsTakenOver = ImmutableSLList.nil();
            indices = new TacletIndex[ruleSets.size()];
            notSimplifiableCaches = (Map<Term, Term>[]) new LRUCache[indices.length];
            int i = 0;
            ImmutableList<String> done = ImmutableSLList.nil();
            for (String ruleSet : ruleSets) {
                ImmutableList<Taclet> taclets = tacletsForRuleSet(proof, ruleSet, done);
                indices[i] = TacletIndexKit.getKit().createTacletIndex(taclets);
                notSimplifiableCaches[i] = new LRUCache<>(DEFAULT_CACHE_SIZE);
                i++;
                done = done.prepend(ruleSet);
            }
        }
    }


    /**
     * Deactivate one-step simplification: clear caches, restore taclets to the goals' taclet
     * indices.
     */
    public synchronized void shutdownIndices() {
        if (lastProof != null) {
            if (!lastProof.isDisposed()) {
                // We need to treat all goals here instead of just open goals;
                // otherwise pruning a (partially) closed proof leads to errors where
                // some rule applications are missing.
                for (Goal g : lastProof.allGoals()) {
                    g.ruleAppIndex().addNoPosTacletApp(appsTakenOver);
                    g.getRuleAppManager().clearCache();
                    g.ruleAppIndex().clearIndexes();
                }
            }
            applicabilityCache.clear();
            lastProof = null;
            appsTakenOver = null;
            indices = null;
            notSimplifiableCaches = null;
        }
    }


    /**
     * returns true if the indices are shutdown
     */
    public boolean isShutdown() {
        return indices == null;
    }

    /**
     * Helper for simplifyPosOrSub. Performs a single step of simplification locally at the given
     * position using the given taclet index.
     *
     * @param protocol
     */
    private SequentFormula simplifyPos(Goal goal, Services services, PosInOccurrence pos,
            int indexNr, Protocol protocol, Map<TermReplacementKey, PosInOccurrence> context,
            /* out */ Set<PosInOccurrence> ifInsts, RuleApp ruleApp) {
        final ImmutableList<NoPosTacletApp> apps =
            indices[indexNr].getRewriteTaclet(pos, TacletFilter.TRUE, services);
        for (TacletApp app : apps) {
            app = app.setPosInOccurrence(pos, services);
            if (app == null) {
                continue;
            }
            if (!app.complete()) {
                app = app.tryToInstantiate(services);
                if (app == null) {
                    continue;
                }
            }
            RewriteTaclet taclet = (RewriteTaclet) app.rule();
            SequentFormula result =
                taclet.getRewriteResult(goal, new TermLabelState(), services, app);
            if (protocol != null) {
                if (ENABLE_PROTOCOL) {
                    protocol.add(app);
                } else {
                    protocol.add(null); // to keep size correct
                }
            }

            // applicable check: only consider normal rule apps
            // (not replace-knowns)
            if (applicableCheck) {
                return result;
            }
            // do replace-known until done
            while (true) {
                // may need to move position up in term due to changes in result
                while (!pos.posInTerm().existsSubTerm(result.formula()) && pos.isTopLevel()) {
                    pos = pos.up();
                }
                Term replacedKnown =
                    replaceKnownHelper(context, result.formula(), result.formula(), pos.isInAntec(),
                        ifInsts, protocol, services, goal, ruleApp, pos.posInTerm(),
                        PosInTerm.getTopLevel());
                if (replacedKnown != null && replacedKnown != result.formula()) {
                    result = new SequentFormula(replacedKnown);
                } else {
                    break;
                }
            }

            return result;
            // TODO Idea: return new Pair<TacletApp, SequentFormula>(null, null);
        }
        return null;
    }


    /**
     * Helper for simplifyPosOrSub. Performs a single step of simplification recursively at a
     * subterm of the given position using the given taclet index.
     *
     * @param protocol
     */
    private SequentFormula simplifySub(Goal goal, Services services, PosInOccurrence pos,
            int indexNr, Protocol protocol, Map<TermReplacementKey, PosInOccurrence> context,
            /* out */ Set<PosInOccurrence> ifInsts, RuleApp ruleApp) {
        for (int i = 0, n = pos.subTerm().arity(); i < n; i++) {
            SequentFormula result =
                simplifyPosOrSub(goal, services, pos.down(i), indexNr, protocol, context, ifInsts,
                    ruleApp);
            if (result != null) {
                return result;
            }
        }
        return null;
    }


    /**
     * Performs a single step of simplification at the given position or its subterms using the
     * given taclet index.
     *
     * @param protocol
     */
    private SequentFormula simplifyPosOrSub(Goal goal, Services services, PosInOccurrence pos,
            int indexNr, Protocol protocol, Map<TermReplacementKey, PosInOccurrence> context,
            /* out */ Set<PosInOccurrence> ifInsts, RuleApp ruleApp) {
        final Term term = pos.subTerm();
        if (notSimplifiableCaches[indexNr].get(term) != null) {
            return null;
        }

        // the core loop of the simplifier:
        // - if the ruleset is to be applied bottom-up, first recurse into subformulas
        // - otherwise, check for applicable rules on the current pos
        // - simplifications are applied recursively
        SequentFormula result;
        if (bottomUp[indexNr]) {
            result = simplifySub(goal, services, pos, indexNr, protocol, context, ifInsts, ruleApp);
            if (result == null) {
                result =
                    simplifyPos(goal, services, pos, indexNr, protocol, context, ifInsts, ruleApp);
            }
        } else {
            result = simplifyPos(goal, services, pos, indexNr, protocol, context, ifInsts, ruleApp);
            if (result == null) {
                result =
                    simplifySub(goal, services, pos, indexNr, protocol, context, ifInsts, ruleApp);
            }
        }

        if (result == null) {
            notSimplifiableCaches[indexNr].put(term, term);
        }

        return result;
    }


    /**
     * Helper for replaceKnown (handles recursion).
     *
     * @param map the context (sequent formulas mapped to their position)
     * @param topIn the formula to simplify (not modified by recursive calls)
     * @param in the term to simplify
     * @param inAntecedent whether the term is in the antecedent
     * @param ifInsts filled by this method with positions used as replace-known targets
     * @param protocol filled by this method with replaceKnown taclet apps
     * @param services services
     * @param goal the goal we work on
     * @param ruleApp the current OSS rule app
     * @param pio indicates which sub-term inside term in is going to be recursed into
     * @param inPio the position of term in inside its sequent formula (always pass top-level
     *        unless you are recursing inside this method)
     * @return the simplified term
     */
    private Term replaceKnownHelper(Map<TermReplacementKey, PosInOccurrence> map, Term topIn,
            Term in,
            boolean inAntecedent, /* out */ Set<PosInOccurrence> ifInsts, Protocol protocol,
            Services services, Goal goal, RuleApp ruleApp, PosInTerm pio, PosInTerm inPio) {
        if (pio == PosInTerm.getTopLevel()) {
            pio = null;
        }
        // search context for our term
        final PosInOccurrence pos = map.get(new TermReplacementKey(in));
        if (pos != null) {
            // match found => replace-known can be applied
            ifInsts.add(pos);
            if (protocol != null) {
                if (ENABLE_PROTOCOL) {
                    protocol.add(
                        makeReplaceKnownTacletApp(topIn, inAntecedent, pos, inPio, goal.sequent()));
                } else {
                    protocol.add(null); // to keep size correct
                }
            }
            Term result =
                pos.isInAntec() ? services.getTermBuilder().tt() : services.getTermBuilder().ff();
            // TODO: pos.subTerm() == in should be true which is currently not the case (labels are
            // missing)
            ImmutableArray<TermLabel> labels =
                TermLabelManager.instantiateLabels(new TermLabelState(), services, in, pos, this,
                    ruleApp, goal, null, null, result);
            if (labels != null && !labels.isEmpty()) {
                result = services.getTermBuilder().label(result, labels);
            }
            return result;
        } else if (in.op() instanceof Modality || in.op() instanceof UpdateApplication
                || in.op() instanceof Transformer) {
            return in;
        } else {
            Term[] subs = new Term[in.arity()];
            boolean changed = false;
            for (int i = 0; i < subs.length; i++) {
                if (changed || (pio != null && pio.getIndexAt(0) != i)) {
                    // only do one change per replaceKnownHelper call.
                    // second part of condition indicates the subformula has not changed
                    // (meaning we can skip recursing)
                    subs[i] = in.sub(i);
                    continue;
                }
                subs[i] = replaceKnownHelper(map, topIn, in.sub(i), inAntecedent, ifInsts, protocol,
                    services, goal, ruleApp, pio != null ? pio.sub() : null, inPio.down(i));
                if (subs[i] != in.sub(i)) {
                    changed = true;
                }
            }
            if (changed) {
                // re-construct term with modified subs array
                return services.getTermBuilder().tf().createTerm(in.op(), subs, in.boundVars(),
                    in.javaBlock(), in.getLabels());
            } else {
                return in;
            }
        }
    }


    /**
     * Simplifies the given constrained formula as far as possible using the replace-known rules
     * (hardcoded here).
     *
     * @param services the services of the current proof
     * @param cf the sequent formula to simplify
     * @param inAntecedent whether the formula is in the antecedent
     * @param context sequent formulas available for replace-known (one entry for each formula on
     *        the sequent)
     * @param ifInsts will contain the positions of used context formulas
     * @param protocol will be filled with replace-known taclet apps
     * @param goal the goal the OSS is currently working on
     * @param ruleApp the current (incomplete) OSS rule app
     * @return the simplified formula (null if no simplification possible)
     */
    private SequentFormula replaceKnown(Services services, SequentFormula cf, boolean inAntecedent,
            Map<TermReplacementKey, PosInOccurrence> context,
            /* out */ Set<PosInOccurrence> ifInsts, Protocol protocol, Goal goal,
            RuleApp ruleApp) {
        if (context == null) {
            return null;
        }
        final Term formula = cf.formula();
        final Term simplifiedFormula = replaceKnownHelper(context, formula, formula, inAntecedent,
            ifInsts,
            protocol, services, goal, ruleApp, PosInTerm.getTopLevel(), PosInTerm.getTopLevel());
        if (simplifiedFormula.equals(formula)) {
            return null;
        } else {
            return new SequentFormula(simplifiedFormula);
        }
    }

    /**
     * Make a new replace-known taclet app with the given parameters:
     * topLevelFormula, inAntecedent and posInFormula specify the application target,
     * pio specifies what formula is referenced in the replace-known's find.
     *
     * @param topLevelFormula term where we apply the replace-known
     * @param inAntecedent whether the top level formula is in the antecedent
     * @param pio the position of the referenced sequent formula
     * @param posInFormula position in topLevelFormula where we apply the replace-known
     * @param sequent sequent of current node
     * @return the replace-known taclet app
     */
    private RuleApp makeReplaceKnownTacletApp(Term topLevelFormula, boolean inAntecedent,
            PosInOccurrence pio, PosInTerm posInFormula,
            Sequent sequent) {
        FindTaclet taclet;
        if (pio.isInAntec()) {
            taclet = (FindTaclet) lastProof.getInitConfig()
                    .lookupActiveTaclet(new Name("replace_known_left"));
        } else {
            taclet = (FindTaclet) lastProof.getInitConfig()
                    .lookupActiveTaclet(new Name("replace_known_right"));
        }

        SVInstantiations svi = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        FormulaSV sv = SchemaVariableFactory.createFormulaSV(new Name("b"));
        svi.add(sv, pio.sequentFormula().formula(), lastProof.getServices());

        // where the replace-known is applied
        PosInOccurrence applicationPIO =
            new PosInOccurrence(new SequentFormula(topLevelFormula), posInFormula,
                inAntecedent); // It is required to create a new PosInOccurrence because formula and
                               // pio.constrainedFormula().formula() are only equals module
                               // renamings and term labels
        ImmutableList<IfFormulaInstantiation> ifInst = ImmutableSLList.nil();
        // create if insts based on pio
        ifInst =
            ifInst.append(new IfFormulaInstSeq(sequent, pio.isInAntec(), pio.sequentFormula()));
        return PosTacletApp.createPosTacletApp(taclet, svi, ifInst, applicationPIO,
            lastProof.getServices());
    }

    /**
     * Simplifies the passed constrained formula using a single taclet or arbitrarily many
     * replace-known steps.
     *
     * @param protocol
     */
    private SequentFormula simplifyConstrainedFormula(Services services, SequentFormula cf,
            boolean inAntecedent, Map<TermReplacementKey, PosInOccurrence> context,
            /* out */ Set<PosInOccurrence> ifInsts, Protocol protocol, Goal goal,
            RuleApp ruleApp) {
        for (int i = 0; i < indices.length; i++) {
            PosInOccurrence pos = new PosInOccurrence(cf, PosInTerm.getTopLevel(), inAntecedent);
            SequentFormula result =
                simplifyPosOrSub(goal, services, pos, i, protocol, context, ifInsts, ruleApp);
            if (result != null) {
                return result;
            }
        }

        return null;
    }


    /**
     * Freshly computes the overall simplification result for the passed constrained formula.
     *
     * @param protocol
     */
    private Instantiation computeInstantiation(Services services, PosInOccurrence ossPIO,
            Sequent seq, Protocol protocol, Goal goal, RuleApp ruleApp) {
        // collect context formulas (potential if-insts for replace-known)
        final Map<TermReplacementKey, PosInOccurrence> context =
            new LinkedHashMap<>();
        SequentFormula cf = ossPIO.sequentFormula();
        for (SequentFormula ante : seq.antecedent()) {
            if (!ante.equals(cf) && ante.formula().op() != Junctor.TRUE) {
                context.put(new TermReplacementKey(ante.formula()),
                    new PosInOccurrence(ante, PosInTerm.getTopLevel(), true));
            }
        }
        for (SequentFormula succ : seq.succedent()) {
            if (!succ.equals(cf) && succ.formula().op() != Junctor.FALSE) {
                context.put(new TermReplacementKey(succ.formula()),
                    new PosInOccurrence(succ, PosInTerm.getTopLevel(), false));
            }
        }
        final Set<PosInOccurrence> ifInsts = new HashSet<>();

        // first, do replace-known applications.
        // If we could only do replace-knowns, OSS should not be applicable
        // => check for that
        if (!applicableCheck) {
            // repeat replace-known until ...
            while (true) {
                SequentFormula result = replaceKnown(services, cf, ossPIO.isInAntec(), context,
                    ifInsts, protocol, goal, ruleApp);
                if (result != null) {
                    cf = result;
                } else {
                    // no more result = no more replace-known possible
                    break;
                }
            }
        }

        // simplify as long as possible
        Collection<SequentFormula> seen = new ArrayList<>();
        SequentFormula simplifiedCf = cf;
        SequentFormula lastCf = null;
        while (true) {
            simplifiedCf = simplifyConstrainedFormula(services, simplifiedCf, ossPIO.isInAntec(),
                context, ifInsts, protocol, goal, ruleApp);
            if (simplifiedCf != null && !seen.contains(simplifiedCf)) {
                if (ENABLE_CYCLE_CHECK) {
                    seen.add(simplifiedCf);
                }
                // optimization: use a set for more efficient contains() check
                // (only helpful for longer OSS)
                if (seen.size() == 30 && seen instanceof ArrayList<SequentFormula>) {
                    seen = new HashSet<>(seen);
                }
                lastCf = simplifiedCf;
            } else {
                break;
            }
        }

        PosInOccurrence[] ifInstsArr = ifInsts.toArray(new PosInOccurrence[0]);
        ImmutableList<PosInOccurrence> immutableIfInsts =
            ImmutableSLList.<PosInOccurrence>nil().append(ifInstsArr);
        return new Instantiation(lastCf, protocol != null ? protocol.size() : seen.size(),
            immutableIfInsts);
    }


    /**
     * Tells whether the passed formula can be simplified
     */
    private synchronized boolean applicableTo(Services services, SequentFormula cf,
            boolean inAntecedent, Goal goal, RuleApp ruleApp) {
        final Boolean b = applicabilityCache.get(cf);
        if (b != null) {
            return b;
        } else {
            // try one simplification step without replace-known
            applicableCheck = true;
            final SequentFormula simplifiedCf = simplifyConstrainedFormula(services, cf,
                inAntecedent, null, null, null, goal, ruleApp);
            applicableCheck = false;
            final boolean result = simplifiedCf != null && !simplifiedCf.equals(cf);
            applicabilityCache.put(cf, result);
            return result;
        }
    }

    private synchronized void refresh(Proof proof) {
        ProofSettings settings = proof.getSettings();
        if (settings == null) {
            settings = ProofSettings.DEFAULT_SETTINGS;
        }

        final boolean newActive = settings.getStrategySettings().getActiveStrategyProperties()
                .get(StrategyProperties.OSS_OPTIONS_KEY).equals(StrategyProperties.OSS_ON);

        if (active != newActive || lastProof != proof || // The setting or proof has changed.
                (isShutdown() && !proof.closed())) { // A closed proof was pruned.
            active = newActive;
            if (active && !proof.closed()) {
                initIndices(proof);
            } else {
                shutdownIndices();
            }
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Enables or disables the one step simplification, depending on the strategy setting made.
     * <strong>IMPORTANT:</strong> This won't do any good if called <i>before</i> the strategy has
     * been set / changed for the current proof. So make sure that everything is done in proper
     * order.
     *
     * @param proof The {@link Proof} for which to refresh the {@link OneStepSimplifier} instance.
     */
    public static void refreshOSS(Proof proof) {
        OneStepSimplifier simplifierInstance = MiscTools.findOneStepSimplifier(proof);
        if (simplifierInstance != null) {
            simplifierInstance.refresh(proof);
        }
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // abort if switched off
        if (!active) {
            return false;
        }

        // abort if not top level constrained formula
        if (pio == null || !pio.isTopLevel()) {
            return false;
        }

        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }

        // applicable to the formula?
        return applicableTo(goal.proof().getServices(), pio.sequentFormula(), pio.isInAntec(), goal,
            null);
    }

    @NonNull
    @Override
    public synchronized ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {

        assert ruleApp instanceof OneStepSimplifierRuleApp
                : "The rule app must be suitable for OSS";
        OneStepSimplifierRuleApp ossRuleApp = (OneStepSimplifierRuleApp) ruleApp;

        final PosInOccurrence pos = ruleApp.posInOccurrence();
        assert pos != null && pos.isTopLevel();

        Protocol protocol = new Protocol();

        Sequent seq = goal.sequent();
        // restrict sequent view to the formulas specified in the rule application
        // this avoids different simplification results if a proof is reloaded
        if (ossRuleApp.shouldRestrictAssumeInsts() && !disableOSSRestriction) {
            ImmutableList<PosInOccurrence> ifInsts = ossRuleApp.ifInsts();
            ImmutableList<SequentFormula> anteFormulas = ImmutableSLList.nil();
            ImmutableList<SequentFormula> succFormulas = ImmutableSLList.nil();
            if (ifInsts != null) {
                for (PosInOccurrence it : ifInsts) {
                    if (it.isInAntec()) {
                        anteFormulas = anteFormulas.prepend(it.sequentFormula());
                    } else {
                        succFormulas = succFormulas.prepend(it.sequentFormula());
                    }
                }
            }
            if (pos.isInAntec()) {
                anteFormulas = anteFormulas.prepend(pos.sequentFormula());
            } else {
                succFormulas = succFormulas.prepend(pos.sequentFormula());
            }
            Semisequent antecedent = anteFormulas.isEmpty() ? Semisequent.EMPTY_SEMISEQUENT
                    : new Semisequent(anteFormulas);
            Semisequent succedent = succFormulas.isEmpty() ? Semisequent.EMPTY_SEMISEQUENT
                    : new Semisequent(succFormulas);
            seq = Sequent.createSequent(antecedent, succedent);
        }
        // get instantiation
        final Instantiation inst =
            computeInstantiation(services, pos, seq, protocol, goal, ruleApp);

        ((OneStepSimplifierRuleApp) ruleApp).setProtocol(protocol);

        // change goal, set if-insts
        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();
        resultGoal.changeFormula(inst.getCf(), pos);
        goal.setBranchLabel(
            inst.getNumAppliedRules() + (inst.getNumAppliedRules() > 1 ? " rules" : " rule"));
        ((IBuiltInRuleApp) ruleApp).setIfInsts(inst.getIfInsts());


        return result;
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

    /**
     * Gets an immutable set containing all the taclets captured by the OSS.
     *
     * @return the captured taclets (as NoPosTacletApps)
     */
    public Set<NoPosTacletApp> getCapturedTaclets() {
        Set<NoPosTacletApp> result = new LinkedHashSet<>();
        synchronized (this) {
            for (TacletIndex index : indices) {
                result.addAll(index.allNoPosTacletApps());
            }
        }
        return result;
    }


    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class Instantiation {
        private final SequentFormula cf;
        private final int numAppliedRules;
        private final ImmutableList<PosInOccurrence> ifInsts;

        public Instantiation(SequentFormula cf, int numAppliedRules,
                ImmutableList<PosInOccurrence> ifInsts) {
            assert numAppliedRules >= 0;
            this.cf = cf;
            this.numAppliedRules = numAppliedRules;
            this.ifInsts = ifInsts;
        }

        public SequentFormula getCf() {
            return cf;
        }

        public int getNumAppliedRules() {
            return numAppliedRules;
        }

        public ImmutableList<PosInOccurrence> getIfInsts() {
            return ifInsts;
        }

        public String toString() {
            return cf + " (" + numAppliedRules + (numAppliedRules > 1 ? " rules)" : "rule)");
        }
    }

    @Override
    public OneStepSimplifierRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new OneStepSimplifierRuleApp(this, pos);
    }

    /**
     * Instances of this class are used in the {@link Map} of
     * {@link OneStepSimplifier#replaceKnown} to
     * forece the same behavior as in Taclet rules where names of logical variables and
     * {@link TermLabel}s are ignored.
     *
     * @author Martin Hentschel
     */
    private static class TermReplacementKey {
        /**
         * The {@link Term} to represent.
         */
        private final Term term;

        /**
         * Constructor.
         *
         * @param term The {@link Term} to represent.
         */
        public TermReplacementKey(Term term) {
            assert term != null;
            this.term = term;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int hashCode() {
            // Allow more conflicts to ensure that naming and term labels are ignored.
            return Objects.hash(term.op(), term.depth());
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof TermReplacementKey) {
                obj = ((TermReplacementKey) obj).term;
            }
            if (obj instanceof Term t) {
                return term.equalsModRenaming(t); // Ignore naming and term labels in the way a
                                                  // taclet rule does.
            } else {
                return false;
            }
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return term.toString();
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
