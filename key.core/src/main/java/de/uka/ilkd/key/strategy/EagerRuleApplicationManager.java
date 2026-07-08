/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.indexing.FormulaTag;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.FormulaChangeInfo;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * Eagerly-maintained rule-application manager (opt-in via the general setting
 * {@link de.uka.ilkd.key.settings.GeneralSettings#isEagerRuleQueueEnabled()} or
 * {@code -Dkey.queue.eager}; design record in {@code queue-redesign-architecture.md}).
 * In contrast to the lazily revalidating {@link QueueRuleApplicationManager}, which discovers
 * staleness only when an entry surfaces at pop, sequent-change events update the candidate set at
 * report time:
 * <ul>
 * <li><b>Identity-anchored pending index</b>: find-taclet candidates are keyed by (formula tag,
 * find-subterm IDENTITY, rule, position). A structure-moving rewrite (e.g. polynomial insertion
 * sort) leaves moved subterms identity-shared; a re-report at an existing position with an
 * unchanged update context is a SURVIVOR (demoted to its last-report tag, lazily at
 * pop-surfacing), a sibling whose recorded position no longer resolves is MOVED (cost snapshot
 * reused, no strategy re-evaluation), and only genuinely new candidates pay a full cost
 * computation at birth.</li>
 * <li><b>Eager dead removal</b>: on {@link #sequentChanged}, candidates anchored on the rebuilt
 * spine of each modification (the terms that ceased to exist) are removed from the active set —
 * the pop loop no longer wades through dead mass. {@code completeRuleApp}'s internal validation
 * remains as a safety net for the few stragglers (pattern-consumed nodes, removed formulas).</li>
 * <li><b>TOP tombstones</b>: a stable-cost candidate whose birth evaluates to TOP is memoized in
 * its pending slot, so re-reports of never-applicable candidates stop paying cost
 * computations.</li>
 * <li><b>Strict-total-order active set</b>: a {@link TreeSet} ordered by the v1 container order
 * (cost, then the deterministic position/rule/instantiation tie-break) with an insertion serial
 * as final disambiguator — deterministic across runs, stable under re-anchoring.</li>
 * </ul>
 *
 * Assumes-base parking, the round discipline and TOP filtering replicate v1 semantics; the gate
 * ladder (removeDup, gemplus, selA32 rule-trace, RunAllProofs) reproduces v1's proofs exactly.
 */
public class EagerRuleApplicationManager implements RuleApplicationManager<Goal> {

    /** System property forcing the manager on/off (CI and benchmarks), overriding the setting. */
    public static final String EAGER_QUEUE_PROPERTY = "key.queue.eager";

    /**
     * @return whether a newly created goal should use the eager manager: the
     *         {@link #EAGER_QUEUE_PROPERTY} system property if set, otherwise the machine-wide
     *         {@link de.uka.ilkd.key.settings.GeneralSettings#isEagerRuleQueueEnabled()} setting.
     *         The queue manager is prover infrastructure orthogonal to the proof strategy, so it
     *         is a general setting (presented on the prover settings pane), not a strategy
     *         property; it takes effect for proofs loaded/started afterwards.
     */
    public static boolean isSelected() {
        final String override = System.getProperty(EAGER_QUEUE_PROPERTY);
        if (override != null) {
            return Boolean.parseBoolean(override);
        }
        return de.uka.ilkd.key.settings.ProofIndependentSettings.DEFAULT_INSTANCE
                .getGeneralSettings().isEagerRuleQueueEnabled();
    }

    /**
     * Ordered active set entry. Order = v1's container order (cost, then the deterministic
     * position/rule/instantiation tie-break -- the select-CSE strategy is tuned against exactly
     * this band ordering; a plain insertion-serial tie-break sends it into applyEqReverse/eqSymm
     * churn), with the insertion serial as the final disambiguator so the order is strictly
     * total for the TreeSet. The comparison uses the immutable BIRTH container ({@link #orderKey})
     * so re-anchoring (which replaces {@link #container} with one at a new position, same cost)
     * can never disturb the set invariants.
     */
    private static final class Entry implements Comparable<Entry> {
        RuleAppContainer container;
        final RuleAppContainer orderKey;
        final long serial;
        /**
         * goal time at which this entry was (re-)expanded; same-round failures are not
         * re-expanded again within the round (v1's workingList discipline).
         */
        long bornRound = -1;
        /** cost epoch at creation (see {@code costEpoch}). */
        long bornEpoch = 0;
        /**
         * Lazy demotion: a re-report arrived for this entry (v1 would kill+re-birth it at
         * cost+now). Instead of paying the TreeSet remove/insert per re-report, the entry is
         * re-tagged when it SURFACES at pop -- it can never complete at its stale tag, which is
         * order-equivalent to eager demotion.
         */
        boolean stale = false;
        /**
         * goal time of the LAST re-report (v1's rebirth tag uses the report time, not the
         * surfacing time -- required for bit-parity with v1).
         */
        long staleTime = -1;
        /**
         * TOP-cost memo: occupies the pending slot only, never the
         * active queue; a same-context re-report at this identity is a no-op.
         */
        boolean tombstone = false;

        Entry(RuleAppContainer container, long serial) {
            this.container = container;
            this.orderKey = container;
            this.serial = serial;
        }

        @Override
        public int compareTo(Entry o) {
            final int c = orderKey.compareTo(o.orderKey);
            if (c != 0) {
                return c;
            }
            return Long.compare(serial, o.serial);
        }
    }

    /**
     * Cost epoch: bumped whenever a GLOBAL input of volatile strategy costs changes -- the count
     * of program-containing formulas (cheap via the cached
     * {@code JTerm.containsJavaBlockRecursive} flag) and goal splits (branch count). A non-stable
     * survivor keeps its tag while the epoch is unchanged (its volatile inputs cannot have moved)
     * and is replaced at current cost when it did -- the cheap form of v1's rebirth-duplicates.
     */
    private long costEpoch = 0;
    /** #formulas containing a program; -1 = not yet initialized. */
    private int programFormulaCount = -1;
    /** Per-manager fast front for {@link CostReuse#eligibility} (which is proof-cached itself). */
    private final IdentityHashMap<Object, Integer> stableCache = new IdentityHashMap<>();

    private @Nullable Goal goal = null;
    private @Nullable TreeSet<Entry> active = null;
    /**
     * (tag, find-subterm identity, rule, position) -> live entry; only index-reported find
     * containers. The POSITION level is essential: subterms are DAG-shared, so one (tag, subterm,
     * rule) triple can have several simultaneous candidates at different positions -- collapsing
     * them (the Phase-1/2 design) silently swallowed sibling candidates.
     */
    private @Nullable HashMap<FormulaTag, IdentityHashMap<Term, HashMap<Object, HashMap<org.key_project.logic.PosInTerm, Entry>>>> pending =
        null;
    private long serialCounter = 0;
    private @Nullable RuleAppContainer previousMinimum = null;
    private @Nullable RuleApp nextRuleApp = null;
    private long nextRuleTime = -1;

    // ---- assumes-base parking (eager's OWN copy; v1 keeps its own identical parking, so the two
    // managers share no parking state -- v1 is untouched, and this copy uses the finer wake key
    // behind FINE_WAKE). ------------------------------------------------------------------------
    /**
     * Parked assumes-incomplete taclet bases, indexed by the concrete top operator(s) of their
     * {@code \assumes} formulas; woken when a formula they could match is added/modified (see
     * {@link #park}/{@link #drainWokenBases}). Insertion-ordered for determinism.
     */
    private @Nullable LinkedHashMap<Operator, Collection<RuleAppContainer>> parkedByOp = null;
    /**
     * Bucket size at which a parking bucket is promoted ArrayList -> LinkedHashSet (O(1) unpark).
     */
    private static final int BUCKET_SET_THRESHOLD = 16;
    /** Top operators of formulas added/modified since the previous round; next round's wake set. */
    private @Nullable LinkedHashSet<Operator> pendingWakeOps = null;

    /**
     * Finer parking wake key (default on). The coarse key is the {@code \assumes} formula's top
     * operator (v1's key); the fine key also folds in structural hashes of the sub-terms the
     * find-match BOUND, so a base for {@code select(h,o,f)=r} wakes only when a
     * {@code select(h,o,f)}
     * -LHS equation changes rather than on every equation -- removing the assumes-churn over-wakes
     * that made the eager queue slower than v1 on assumes-heavy proofs. Sound (a formula that could
     * match the assumes always produces the base's key, so a wake is never missed -- only harmless
     * over-wakes are dropped) but NOT byte-identical to v1: it trades a benign search-order reorder
     * for the churn cut (below v1 timing on SimplifiedLinkedList.remove).
     * <p>
     * A {@code static final} constant so the JIT folds the branch away entirely; flip it to
     * {@code false} and recompile to get the coarse mode, which reproduces v1 byte-for-byte -- the
     * on-demand reproduction/trust check for the eager queue. Either way v1/classic is never
     * touched: this is eager's private parking.
     */
    private static final boolean FINE_WAKE = true;
    private static final long WILDCARD = 0x9E3779B97F4A7C15L; // marks an unbound sub-position
    private static final long FNV_PRIME = 1099511628211L;
    /** Depth cap of the structural hash: deeper structure just folds to its operator. */
    private static final int STRUCT_HASH_DEPTH = 4;
    /** Fine-wake analogue of {@link #parkedByOp}: bases parked by content key. */
    private @Nullable LinkedHashMap<Long, Collection<RuleAppContainer>> parkedByKey = null;
    /** Fine-wake analogue of {@link #pendingWakeOps}. */
    private @Nullable LinkedHashSet<Long> pendingWakeKeys = null;

    /**
     * Completeness safety net: number of EFFECTIVE stall-rescues -- exhausted pop loops where the
     * full re-report reconciliation then DID yield an app, proving a candidate was silently lost.
     * Any nonzero value indicates a loss bug to hunt; the net keeps proofs closing meanwhile.
     * Exhaustions where the retry also finds nothing are the normal end of a goal that ran out of
     * applicable rules and are counted separately.
     */
    public static final java.util.concurrent.atomic.AtomicLong PROBE_RESCUES =
        new java.util.concurrent.atomic.AtomicLong();
    /**
     * Benign twin of {@link #PROBE_RESCUES}: pop exhaustion where the reconciliation retry also
     * found nothing -- the goal genuinely has no applicable rules (bike: 14 open goals).
     */
    public static final java.util.concurrent.atomic.AtomicLong PROBE_EXHAUST_CONFIRMED =
        new java.util.concurrent.atomic.AtomicLong();

    // ------------------------------------------------------------------- lifecycle

    @Override
    public void setGoal(Goal p_goal) {
        goal = p_goal;
    }

    @Override
    public void clearCache() {
        active = null;
        pending = null;
        previousMinimum = null;
        nextRuleApp = null;
        parkedByOp = null;
        pendingWakeOps = null;
        parkedByKey = null;
        pendingWakeKeys = null;
        if (goal != null) {
            goal.proof().getServices().getCaches().getIfInstantiationCache().releaseAll();
        }
    }

    @Override
    public RuleApplicationManager<Goal> copy() {
        return (RuleApplicationManager<Goal>) clone();
    }

    @Override
    public Object clone() {
        final EagerRuleApplicationManager res = new EagerRuleApplicationManager();
        res.serialCounter = serialCounter;
        res.previousMinimum = previousMinimum;
        res.programFormulaCount = programFormulaCount;
        // a split changes the branch count -- a global volatile-cost input
        res.costEpoch = costEpoch + 1;
        // eager's own parking state: parked bases must survive goal splits (losing them silently
        // discards every parked candidate on both branches -- the selA32 ladder stall)
        copyParkingInto(res);
        if (active != null) {
            // Entries carry a mutable container reference (re-anchoring); split goals must not
            // alias them. Deep-copy entries, rebuild the identity index.
            res.active = new TreeSet<>();
            res.pending = new HashMap<>();
            for (Entry e : active) {
                final Entry copy = new Entry(e.container, e.serial);
                copy.bornEpoch = e.bornEpoch;
                // carry pending demotions: v1's children inherit the rebirth-tagged container,
                // so a demotion flagged but not yet consumed at surfacing survives the split too
                copy.stale = e.stale;
                copy.staleTime = e.staleTime;
                res.active.add(copy);
                res.indexEntry(copy);
            }
            // Tombstones (pending-only entries) are deliberately NOT copied: dropping them on a
            // split is sound (the child re-evaluates once per memoized identity and lays its own
            // memo), while copying costs an O(pending) walk PER SPLIT -- measured +14% wall and
            // +156MB on split-heavy gemplus for a 0.33 hit/creation ratio. The memo pays off on
            // re-report storms within a goal (ips4o: 20.6 hits/creation), not across splits.
        }
        return res;
    }

    // ------------------------------------------------------------------- events

    private void ensureInitialized() {
        if (active != null) {
            return;
        }
        if (goal == null) {
            clearCache();
            return;
        }
        programFormulaCount = 0;
        for (boolean antec : new boolean[] { true, false }) {
            for (SequentFormula sf : (antec ? goal.sequent().antecedent()
                    : goal.sequent().succedent())) {
                if (((de.uka.ilkd.key.logic.JTerm) sf.formula()).containsJavaBlockRecursive()) {
                    programFormulaCount++;
                }
            }
        }
        active = new TreeSet<>();
        pending = new HashMap<>();
        previousMinimum = null;
        goal.ruleAppIndex().reportAutomatedRuleApps(goal.getRuleAppManager(),
            goal.proof().getServices());
    }

    @Override
    public void ruleAdded(RuleApp rule, PosInOccurrence pos) {
        if (active == null) {
            return;
        }
        if (pos != null && rule instanceof de.uka.ilkd.key.rule.NoPosTacletApp npta) {
            final FormulaTag tag =
                goal.getFormulaTagManager().getTagForPos(pos.topLevel());
            if (tag != null) {
                final HashMap<org.key_project.logic.PosInTerm, Entry> bucket =
                    bucketFor(tag, pos.subTerm(), rule.rule());
                if (bucket != null) {
                    final Entry atPos = bucket.get(pos.posInTerm());
                    if (atPos != null && atPos.container instanceof FindTacletAppContainer f
                            && f.getFindSubterm() == pos.subTerm()) {
                        if (atPos.tombstone) {
                            if (sameUpdateContext(
                                f.getTacletApp().instantiations().getUpdateContext(),
                                npta.instantiations().getUpdateContext())) {
                                // TOP memo still valid: STABLE cost at an unchanged identity and
                                // context is still TOP (see Entry#tombstone) -- skip the recompute.
                                return;
                            }
                            // update context changed: the memo's inputs moved, re-evaluate via a
                            // fresh birth (which may lay a new tombstone)
                            bucket.remove(pos.posInTerm());
                        } else
                        // SURVIVOR: same subterm at the same position -- in v1 this candidate
                        // survives the modification untouched (independent subformula) and keeps
                        // its original virtual-time tag. BUT only if its recorded update context
                        // is unchanged: v1 kills same-position apps whose PRECEDING UPDATE changed
                        // (updateContextIsRecorded) and replaces them from the fresh report --
                        // swallowing that report here loses program rules on update targets.
                        if (sameUpdateContext(
                            f.getTacletApp().instantiations().getUpdateContext(),
                            npta.instantiations().getUpdateContext())) {
                            // DEMOTE-ON-RE-REPORT (v1 semantics): v1 kills a re-reported
                            // candidate positionally and re-births it at cost+NOW. Keeping the
                            // original tag instead lets ever-fresh cheap-band survivors starve
                            // positive-cost program rules (measured: gemplus SE starvation).
                            if (costLocality(f.getTacletApp().taclet()) != COST_VOLATILE) {
                                // STABLE/WEAK cost: LAZY demotion -- flag in O(1); the re-tag
                                // (stable: cached ageFreeCost; weak: surfacing recompute, which
                                // is report-equivalent since the find formula's state at
                                // surfacing equals its state at the LAST report) happens at
                                // pop-surfacing.
                                atPos.stale = true;
                                atPos.staleTime = goal.getTime();
                                return;
                            }
                            // VOLATILE cost (e.g. cut_direct, whose cost flips TOP<->finite on
                            // OTHER formulas' content): must be re-costed AT REPORT TIME,
                            // exactly like v1's rebirth -- surfacing-time recompute was tried
                            // and refuted (removeDup diverges). Replace and fall through to a
                            // full birth.
                            active.remove(atPos);
                            bucket.remove(pos.posInTerm());
                        } else {
                            // context changed: replace with a full rebirth (context-dependent
                            // costs must be recomputed; the old instantiations are invalid)
                            active.remove(atPos);
                            bucket.remove(pos.posInTerm());
                        }
                    }
                    // MOVE detection: a sibling entry whose recorded position no longer
                    // resolves to the shared subterm is the one this report re-anchors.
                    // The stale entry is removed and the report falls through to a FULL
                    // birth (computeCost at the new position, current time) -- exactly
                    // v1's kill+rebirth. The old ageFreeCost must NOT be transferred:
                    // STABLE locality is "fixed by app + match + find subterm + PATH +
                    // context", i.e. it may be position-DEPENDENT (e.g. find-depth cost
                    // terms: replaceKnownSelect pays +10 per nesting level), so a cost
                    // computed at the old depth mis-tags the entry at the new one by the
                    // depth delta (measured on bike: a depth-4 cost kept at a depth-2
                    // position surfaced 20 too late and reordered the select-CSE band).
                    // The tombstone path refuses move-transfer for the same reason.
                    for (var it = bucket.entrySet().iterator(); it.hasNext();) {
                        final var e = it.next();
                        if (!e.getValue().tombstone
                                && e.getValue().container instanceof FindTacletAppContainer mf
                                && mf.getFindSubterm() == pos.subTerm()
                                && costLocality(
                                    mf.getTacletApp().taclet()) == COST_STABLE
                                && sameUpdateContext(
                                    mf.getTacletApp().instantiations().getUpdateContext(),
                                    npta.instantiations().getUpdateContext())
                                && !resolves(tag, e.getKey(), pos.subTerm())) {
                            active.remove(e.getValue());
                            it.remove();
                            break;
                        }
                    }
                }
            }
        }
        final RuleAppContainer c = RuleAppContainer.createAppContainer(rule, pos, goal);
        if (pos != null
                && c.getCost() == org.key_project.prover.strategy.costbased.TopRuleAppCost.INSTANCE
                && c instanceof FindTacletAppContainer fc
                && costLocality(fc.getTacletApp().taclet()) == COST_STABLE) {
            // memoize the TOP verdict at this identity (see Entry#tombstone): occupies the
            // pending slot only, so same-context re-reports become no-ops instead of recomputes
            final Entry tomb = new Entry(c, serialCounter++);
            tomb.tombstone = true;
            tomb.bornEpoch = costEpoch;
            indexEntry(tomb);
            return;
        }
        insert(c, true);
    }

    /**
     * @return true iff the taclet's strategy cost is fully STABLE (CostReuse locality): fixed by
     *         app + match + find subterm. Only then may a survivor keep its tag or a move reuse
     *         its ageFreeCost; weak-stable/volatile costs must be recomputed after any change --
     *         v1 gets this via its rebirth-duplicates.
     */
    private static final int COST_STABLE = 0;
    private static final int COST_WEAK = 1;
    private static final int COST_VOLATILE = 2;

    /**
     * Three-way cost locality of a taclet (cached per manager over the proof-cached
     * {@link CostReuse#eligibility}):
     * <ul>
     * <li>{@link #COST_STABLE}: cost fixed by app + match + find subterm -- a demoted survivor
     * re-tags from the cached ageFreeCost, no recompute.</li>
     * <li>{@link #COST_WEAK}: cost also reads the find FORMULA. Lazy recompute at pop-surfacing
     * is exact: the formula's state at surfacing equals its state at the LAST report (any later
     * change re-reports and re-flags), so the surfacing recompute sees exactly what v1's
     * report-time rebirth saw.</li>
     * <li>{@link #COST_VOLATILE}: cost may read arbitrary proof state (e.g. cut_direct flips
     * TOP&lt;-&gt;finite on OTHER formulas' content) -- must be re-costed eagerly at report time,
     * exactly like v1's rebirth.</li>
     * </ul>
     */
    private int costLocality(org.key_project.prover.rules.Taclet taclet) {
        final Integer cached = stableCache.get(taclet);
        if (cached != null) {
            return cached;
        }
        final var el = CostReuse.eligibility(goal.getGoalStrategy(), goal.proof(),
            (de.uka.ilkd.key.rule.Taclet) taclet);
        final int locality =
            el == null ? COST_VOLATILE : (el.weakStable() ? COST_WEAK : COST_STABLE);
        stableCache.put(taclet, locality);
        return locality;
    }

    /**
     * @return true iff descending {@code pit} in the tag's CURRENT formula reaches {@code subterm}
     */
    private boolean resolves(FormulaTag tag, org.key_project.logic.PosInTerm pit, Term subterm) {
        final PosInOccurrence top = goal.getFormulaTagManager().getPosForTag(tag);
        if (top == null) {
            return false;
        }
        Term term = (Term) top.sequentFormula().formula();
        for (int i = 0; i < pit.depth(); i++) {
            final int idx = pit.getIndexAt(i);
            if (idx >= term.arity()) {
                return false;
            }
            term = term.sub(idx);
        }
        return term == subterm;
    }

    private @Nullable HashMap<org.key_project.logic.PosInTerm, Entry> bucketFor(FormulaTag tag,
            Term subterm, Object rule) {
        if (pending == null) {
            return null;
        }
        final var byTerm = pending.get(tag);
        if (byTerm == null) {
            return null;
        }
        final var byRule = byTerm.get(subterm);
        return byRule == null ? null : byRule.get(rule);
    }

    @Override
    public void rulesAdded(ImmutableList<? extends RuleApp> rules, PosInOccurrence pos) {
        if (active == null) {
            return;
        }
        for (RuleApp r : rules) {
            ruleAdded(r, pos);
        }
    }

    /**
     * Eager dead removal: the terms along the modification path of the OLD formula ceased to
     * exist; drop their candidates from the active set. Moved subterms keep their (re-anchored)
     * candidates.
     */
    @Override
    public void sequentChanged(SequentChangeInfo sci) {
        if (active == null || pending == null) {
            return;
        }
        recordWakeOps(sci.addedFormulas(true));
        recordWakeOps(sci.addedFormulas(false));
        recordModifiedWakeOps(sci.modifiedFormulas(true));
        recordModifiedWakeOps(sci.modifiedFormulas(false));

        // cost-epoch maintenance: the count of program-containing formulas is the dominant
        // GLOBAL input of volatile strategy costs (sequentContainsNoPrograms and friends); the
        // per-term flag is cached, so this is O(changed formulas)
        if (programFormulaCount >= 0) {
            int delta = 0;
            for (boolean antec : new boolean[] { true, false }) {
                for (SequentFormula sf : sci.addedFormulas(antec)) {
                    if (((de.uka.ilkd.key.logic.JTerm) sf.formula())
                            .containsJavaBlockRecursive()) {
                        delta++;
                    }
                }
                for (SequentFormula sf : sci.removedFormulas(antec)) {
                    if (((de.uka.ilkd.key.logic.JTerm) sf.formula())
                            .containsJavaBlockRecursive()) {
                        delta--;
                    }
                }
                for (FormulaChangeInfo fci : sci.modifiedFormulas(antec)) {
                    final boolean before =
                        ((de.uka.ilkd.key.logic.JTerm) fci.positionOfModification()
                                .sequentFormula().formula()).containsJavaBlockRecursive();
                    final boolean after = ((de.uka.ilkd.key.logic.JTerm) fci.newFormula()
                            .formula()).containsJavaBlockRecursive();
                    delta += (after ? 1 : 0) - (before ? 1 : 0);
                }
            }
            if (delta != 0) {
                programFormulaCount += delta;
                costEpoch++;
            }
        }
        for (boolean antec : new boolean[] { true, false }) {
            for (FormulaChangeInfo fci : sci.modifiedFormulas(antec)) {
                final PosInOccurrence changePos = fci.positionOfModification();
                final SequentFormula oldFormula = changePos.sequentFormula();
                final FormulaTag tag = goal.getFormulaTagManager()
                        .getTagForPos(changePos.topLevel()
                                .replaceSequentFormula(fci.newFormula()));
                // walk the old spine: top-level term down to (and including) the modified
                // subterm -- these objects ceased to exist in the new formula
                final var byTerm = tag == null ? null : pending.get(tag);
                if (byTerm == null) {
                    continue;
                }
                Term spineTerm = (Term) oldFormula.formula();
                final var pit = changePos.posInTerm();
                org.key_project.logic.PosInTerm spinePit =
                    org.key_project.logic.PosInTerm.getTopLevel();
                int i = 0;
                while (true) {
                    // Only the spine POSITION died; the same (DAG-shared) term object may occur
                    // at other, untouched positions whose candidates must survive. Remove exactly
                    // the entry anchored at the spine-prefix position, per rule.
                    final var byRule = byTerm.get(spineTerm);
                    if (byRule != null) {
                        for (var it = byRule.values().iterator(); it.hasNext();) {
                            final var byPit = it.next();
                            final Entry e = byPit.remove(spinePit);
                            if (e != null) {
                                active.remove(e);
                            }
                            if (byPit.isEmpty()) {
                                it.remove();
                            }
                        }
                        if (byRule.isEmpty()) {
                            byTerm.remove(spineTerm);
                        }
                    }
                    if (i >= pit.depth()) {
                        break;
                    }
                    final int idx = pit.getIndexAt(i++);
                    spineTerm = spineTerm.sub(idx);
                    spinePit = spinePit.down(idx);
                }
            }
        }
    }

    // ------------------------------------------------------------------- index helpers

    /**
     * Update prefixes compared by IDENTITY of the recorded update terms: unchanged prefixes are
     * shared term objects, rebuilt prefixes are fresh ones -- identity is exactly "prefix
     * unchanged", and cheap.
     */
    private static boolean sameUpdateContext(
            ImmutableList<de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair> a,
            ImmutableList<de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair> b) {
        while (!a.isEmpty() && !b.isEmpty()) {
            final var x = a.head();
            final var y = b.head();
            if (x != y && x.update() != y.update()) {
                return false;
            }
            a = a.tail();
            b = b.tail();
        }
        return a.isEmpty() && b.isEmpty();
    }

    private void indexEntry(Entry e) {
        if (!(e.container instanceof FindTacletAppContainer f)) {
            return;
        }
        pending.computeIfAbsent(f.getPositionTag(), k -> new IdentityHashMap<>())
                .computeIfAbsent(f.getFindSubterm(), k -> new HashMap<>())
                .computeIfAbsent(f.getTacletApp().rule(), k -> new HashMap<>())
                .put(f.getApplicationPosition().posInTerm(), e);
    }

    private void unindex(Entry e) {
        if (pending == null || !(e.container instanceof FindTacletAppContainer f)) {
            return;
        }
        final var byTerm = pending.get(f.getPositionTag());
        if (byTerm == null) {
            return;
        }
        final var byRule = byTerm.get(f.getFindSubterm());
        if (byRule == null) {
            return;
        }
        final var byPit = byRule.get(f.getTacletApp().rule());
        if (byPit != null
                && byPit.get(f.getApplicationPosition().posInTerm()) == e) {
            byPit.remove(f.getApplicationPosition().posInTerm());
        }
    }

    /** Insert with the current round as birth round (v1's furtherApps-queue semantics). */
    private void insertBornNow(RuleAppContainer c) {
        if (c.getCost() == org.key_project.prover.strategy.costbased.TopRuleAppCost.INSTANCE) {
            return;
        }
        final Entry e = new Entry(c, serialCounter++);
        e.bornEpoch = costEpoch;
        e.bornRound = goal.getTime();
        active.add(e);
    }

    private void insert(RuleAppContainer c, boolean index) {
        // v1 semantics: TOP-cost containers never enter the queue (automode stops when only
        // inapplicable candidates remain; completing one is undefined, cf. pullOut's
        // tryToInstantiate on an unmatched generic skolem)
        if (c.getCost() == org.key_project.prover.strategy.costbased.TopRuleAppCost.INSTANCE) {
            return;
        }
        final Entry e = new Entry(c, serialCounter++);
        e.bornEpoch = costEpoch;
        active.add(e);
        if (index) {
            indexEntry(e);
        }
    }

    // ------------------------------------------------------------------- round

    @Override
    public RuleApp peekNext() {
        ensureInitialized();

        final long currentTime = goal.getTime();
        if (currentTime != nextRuleTime) {
            nextRuleApp = null;
            nextRuleTime = currentTime;
        }
        if (nextRuleApp != null) {
            return nextRuleApp;
        }

        goal.ruleAppIndex().fillCache();

        final var woken = drainWokenBases();
        if (woken != null) {
            for (RuleAppContainer c : woken) {
                insert(c, false);
            }
        }

        if (previousMinimum != null) {
            for (RuleAppContainer c : previousMinimum.createFurtherApps(goal)) {
                // v1 protocol: previousMinimum expansion products enter the furtherApps queue --
                // if they fail completion THIS round they are retried next round WITHOUT another
                // expansion (workingList discipline). Mark them as born this round.
                insertBornNow(c);
            }
            previousMinimum = null;
        }

        boolean rescued = false;
        java.util.ArrayList<Entry> nextRound = null;
        while (nextRuleApp == null && !active.isEmpty()) {
            final Entry min = active.pollFirst();

            // lazy demotion: a re-report arrived since this entry was queued -- v1 would have
            // killed + re-birthed it at cost+now. Re-tag it now (cached ageFreeCost, no
            // computeCost) and continue; it competes at its demoted tag.
            if (min.stale && min.container instanceof FindTacletAppContainer sf) {
                unindex(min);
                // Only re-tag if the entry's position still resolves to its find-subterm on the
                // CURRENT formula -- further changes since the stale-flagging may have killed it
                // positionally (then v1 dropped it too, and any successor lives via its own
                // report).
                if (resolves(sf.getPositionTag(), sf.getApplicationPosition().posInTerm(),
                    sf.getFindSubterm())) {
                    final RuleAppContainer fresh;
                    if (costLocality(sf.getTacletApp().taclet()) == COST_STABLE) {
                        // stable cost: cached ageFreeCost + report-time tag, no computeCost
                        fresh = sf.retaggedCopy(goal, min.staleTime);
                    } else {
                        // WEAK cost: recompute at surfacing (report-equivalent, see
                        // costLocality javadoc); VOLATILE never reaches here (eager at report)
                        final RuleAppContainer recomputed =
                            RuleAppContainer.createAppContainer(sf.getTacletApp(),
                                sf.getPosInOccurrence(goal), goal);
                        if (recomputed
                                .getCost() == org.key_project.prover.strategy.costbased.TopRuleAppCost.INSTANCE) {
                            continue;
                        }
                        // v1 parity: the surviving v1 rebirth for a re-reported candidate is the
                        // duplicate born at the LAST report, tagged ageFreeCost + REPORT time
                        // (all earlier duplicates fail positionally at pop). The recompute above
                        // is needed for the report-equivalent ageFreeCost and the TOP check, but
                        // it stamps the SURFACING time -- re-tag the total cost back to the
                        // report time, exactly like the STABLE branch (removeDup: the
                        // surfacing-time stamp collapsed distinct report tags -1129/-1117 into a
                        // -1109 tie and flipped the select-CSE order).
                        fresh = ((FindTacletAppContainer) recomputed)
                                .retaggedCopy(goal, min.staleTime);
                    }
                    final Entry ne = new Entry(fresh, serialCounter++);
                    ne.bornEpoch = costEpoch;
                    active.add(ne);
                    indexEntry(ne);
                }
                continue;
            }

            final RuleAppContainer c = min.container;

            nextRuleApp = c.completeRuleApp(goal);
            if (nextRuleApp == null) {
                if (c instanceof TacletAppContainer) {
                    if (min.bornRound == currentTime) {
                        // expanded THIS round already and still not completable: retry next
                        // round without re-expansion (v1's workingList discipline; avoids a
                        // same-cost regeneration livelock within the round)
                        if (nextRound == null) {
                            nextRound = new java.util.ArrayList<>();
                        }
                        nextRound.add(min);
                    } else {
                        unindex(min);
                        // veto/instantiation failure or safety-net death: same retry discipline
                        // as v1 -- re-expansion re-costs with the current age (virtual-time
                        // re-tag). An assumes-base whose expansion yields nothing but itself is
                        // PARKED (v1 semantics): it stops churning instances every round and is
                        // woken when a formula with a matching top operator arrives.
                        final var further = c.createFurtherApps(goal);
                        if (further.size() == 1
                                && further.head() instanceof TacletAppContainer base
                                && !base.getTacletApp().assumesInstantionsComplete()
                                && park(base)) {
                            continue;
                        }
                        for (RuleAppContainer f : further) {
                            if (f.getCost() == org.key_project.prover.strategy.costbased.TopRuleAppCost.INSTANCE) {
                                continue;
                            }
                            final Entry e = new Entry(f, serialCounter++);
                            e.bornEpoch = costEpoch;
                            e.bornRound = currentTime;
                            active.add(e);
                        }
                    }
                }
            } else {
                unindex(min);
                previousMinimum = c;
            }
        }
        if (nextRound != null) {
            active.addAll(nextRound);
        }
        if (nextRuleApp == null && !rescued) {
            // completeness safety net: reconcile against a full index re-report before giving
            // up. A goal that legitimately ran out of applicable rules exhausts here too (the
            // retry then finds nothing -- benign, counted as PROBE_EXHAUST_CONFIRMED); only a
            // retry that DOES yield an app proves a silently lost candidate (PROBE_RESCUES,
            // each one a loss bug to hunt).
            rescued = true;
            clearCache();
            ensureInitialized();
            java.util.ArrayList<Entry> rescueRound = null;
            while (nextRuleApp == null && !active.isEmpty()) {
                final Entry min = active.pollFirst();
                RuleApp completed = min.container.completeRuleApp(goal);
                nextRuleApp = completed;
                if (completed == null) {
                    if (min.container instanceof TacletAppContainer) {
                        if (rescueRound == null) {
                            rescueRound = new java.util.ArrayList<>();
                        }
                        min.bornRound = currentTime;
                        rescueRound.add(min);
                    }
                } else {
                    unindex(min);
                    previousMinimum = min.container;
                }
            }
            if (rescueRound != null) {
                active.addAll(rescueRound);
            }
            if (nextRuleApp != null) {
                PROBE_RESCUES.incrementAndGet();
            } else {
                PROBE_EXHAUST_CONFIRMED.incrementAndGet();
            }
        }
        return nextRuleApp;
    }

    @Override
    public RuleApp next() {
        final RuleApp res = peekNext();
        nextRuleApp = null;
        return res;
    }

    // =========================================================================================
    // Assumes-base parking -- eager's OWN copy, decoupled from v1. Two wake keys, selected by the
    // compile-time FINE_WAKE constant: coarse (v1's \assumes top operator, byte-identical to v1) or
    // fine (default; top operator folded with structural hashes of the find-BOUND sub-terms, so a
    // base wakes only when a structurally-matching equation changes). v1/classic keeps its own
    // identical coarse parking, so the two managers share no state -- v1 is untouched.
    // =========================================================================================

    /**
     * Park an assumes-incomplete base, indexing it under the wake key(s) of its {@code \assumes}
     * formulas so it can be woken when a matching formula appears.
     *
     * @return {@code true} if parked; {@code false} if not effectively indexable (an
     *         unbound-generic
     *         {@code \assumes} top), in which case the caller keeps it in the active set
     */
    private boolean park(TacletAppContainer base) {
        if (FINE_WAKE) {
            final List<Long> keys = assumesWakeKeys(base);
            if (keys == null) {
                return false;
            }
            if (parkedByKey == null) {
                parkedByKey = new LinkedHashMap<>();
            }
            for (Long k : keys) {
                Collection<RuleAppContainer> bucket = parkedByKey.get(k);
                if (bucket == null) {
                    bucket = new ArrayList<>(4);
                    parkedByKey.put(k, bucket);
                }
                bucket.add(base);
                if (bucket.size() == BUCKET_SET_THRESHOLD && bucket instanceof ArrayList) {
                    parkedByKey.put(k, new LinkedHashSet<>(bucket));
                }
            }
            return true;
        }
        final List<Operator> ops = assumesWakeOps(base);
        if (ops == null) {
            return false;
        }
        if (parkedByOp == null) {
            parkedByOp = new LinkedHashMap<>();
        }
        for (Operator op : ops) {
            Collection<RuleAppContainer> bucket = parkedByOp.get(op);
            if (bucket == null) {
                bucket = new ArrayList<>(4);
                parkedByOp.put(op, bucket);
            }
            bucket.add(base);
            if (bucket.size() == BUCKET_SET_THRESHOLD && bucket instanceof ArrayList) {
                parkedByOp.put(op, new LinkedHashSet<>(bucket));
            }
        }
        return true;
    }

    /**
     * Collect (and un-park) every parked base waiting on a wake key recorded since the last round;
     * the caller re-inserts them into the active set.
     *
     * @return the woken bases in deterministic insertion order, or {@code null} if none
     */
    private @Nullable Collection<RuleAppContainer> drainWokenBases() {
        if (FINE_WAKE) {
            if (pendingWakeKeys == null) {
                return null;
            }
            LinkedHashSet<RuleAppContainer> woken = null;
            if (parkedByKey != null && !parkedByKey.isEmpty()) {
                for (Long k : pendingWakeKeys) {
                    final Collection<RuleAppContainer> bucket = parkedByKey.get(k);
                    if (bucket != null) {
                        if (woken == null) {
                            woken = new LinkedHashSet<>();
                        }
                        woken.addAll(bucket);
                    }
                }
                if (woken != null) {
                    for (RuleAppContainer c : woken) {
                        unindexParked(c);
                    }
                }
            }
            pendingWakeKeys.clear();
            return woken;
        }
        if (pendingWakeOps == null) {
            return null;
        }
        LinkedHashSet<RuleAppContainer> woken = null;
        if (parkedByOp != null && !parkedByOp.isEmpty()) {
            for (Operator op : pendingWakeOps) {
                final Collection<RuleAppContainer> bucket = parkedByOp.get(op);
                if (bucket != null) {
                    if (woken == null) {
                        woken = new LinkedHashSet<>();
                    }
                    woken.addAll(bucket);
                }
            }
            if (woken != null) {
                for (RuleAppContainer c : woken) {
                    unindexParked(c);
                }
            }
        }
        pendingWakeOps.clear();
        return woken;
    }

    /** Remove a woken container from every operator/key bucket it was parked under. */
    private void unindexParked(RuleAppContainer c) {
        if (!(c instanceof TacletAppContainer tac)) {
            return;
        }
        if (FINE_WAKE) {
            if (parkedByKey == null) {
                return;
            }
            final List<Long> keys = assumesWakeKeys(tac);
            if (keys == null) {
                return;
            }
            for (Long k : keys) {
                final Collection<RuleAppContainer> bucket = parkedByKey.get(k);
                if (bucket != null) {
                    bucket.remove(c);
                    if (bucket.isEmpty()) {
                        parkedByKey.remove(k);
                    }
                }
            }
            return;
        }
        if (parkedByOp == null) {
            return;
        }
        final List<Operator> ops = assumesWakeOps(tac);
        if (ops == null) {
            return;
        }
        for (Operator op : ops) {
            final Collection<RuleAppContainer> bucket = parkedByOp.get(op);
            if (bucket != null) {
                bucket.remove(c);
                if (bucket.isEmpty()) {
                    parkedByOp.remove(op);
                }
            }
        }
    }

    /**
     * The concrete top operator(s) of the {@code \assumes} formulas of the given base, resolved
     * through the find-match's schema-variable instantiations (v1's coarse wake key), or
     * {@code null} if the base is not effectively indexable.
     */
    private static @Nullable List<Operator> assumesWakeOps(TacletAppContainer base) {
        final NoPosTacletApp app = base.getTacletApp();
        final Sequent assumesSeq = app.taclet().assumesSequent();
        if (assumesSeq.isEmpty()) {
            return null;
        }
        final SVInstantiations insts = app.instantiations();
        final List<Operator> ops = new ArrayList<>(assumesSeq.size());
        for (SequentFormula sf : assumesSeq) {
            Operator op = sf.formula().op();
            if (op instanceof SchemaVariable sv) {
                final Object inst = insts.getInstantiation(sv);
                if (!(inst instanceof JTerm instTerm)) {
                    return null; // unbound (or non-term) generic top -> not indexable
                }
                op = instTerm.op();
                if (op instanceof SchemaVariable) {
                    return null; // still schematic -> not indexable
                }
            }
            ops.add(op);
        }
        return ops;
    }

    // ---- fine wake keys (see FINE_WAKE) --------------------------------------------------------

    private static Term stripUpdates(Term t) {
        Term cur = t;
        while (cur.op() instanceof UpdateApplication && cur instanceof JTerm jt) {
            cur = UpdateApplication.getTarget(jt);
        }
        return cur;
    }

    /**
     * A label-, java-block- and bound-variable-agnostic structural hash: operators along the term
     * tree only, capped at a small depth. Deliberately COARSER than {@link Term#hashCode()} (which
     * on this branch still folds label-sensitive sub-hashes): it agrees on at least every pair of
     * terms the {@code \assumes} matcher treats as equal, so a wake key built from it can only
     * over-fire a wake (harmless re-park), never MISS one.
     */
    private static long structHash(Term t, int depth) {
        long h = t.op().hashCode();
        if (depth <= 0) {
            return h;
        }
        for (int i = 0, n = t.arity(); i < n; i++) {
            h = h * FNV_PRIME + structHash(t.sub(i), depth - 1);
        }
        return h;
    }

    /**
     * Fine wake keys of a base: for each {@code \assumes} formula, its top operator folded with the
     * structural hash of each immediate sub-term bound by the find-match (unbound subs = WILDCARD).
     * Uses the same fold as {@link #recordWakeKeys}, so a changed formula that could match this
     * assumes produces this key among its wildcard-subset keys.
     *
     * @return the keys, or {@code null} if not effectively indexable (unbound-generic top)
     */
    private static @Nullable List<Long> assumesWakeKeys(TacletAppContainer base) {
        final NoPosTacletApp app = base.getTacletApp();
        final Sequent assumesSeq = app.taclet().assumesSequent();
        if (assumesSeq.isEmpty()) {
            return null;
        }
        final SVInstantiations insts = app.instantiations();
        final List<Long> keys = new ArrayList<>(assumesSeq.size());
        for (SequentFormula sf : assumesSeq) {
            Term t = stripUpdates(sf.formula());
            Operator top = t.op();
            if (top instanceof SchemaVariable sv) {
                final Object inst = insts.getInstantiation(sv);
                if (!(inst instanceof JTerm it)) {
                    return null;
                }
                t = stripUpdates(it);
                top = t.op();
                if (top instanceof SchemaVariable) {
                    return null;
                }
            }
            long h = top.hashCode();
            final int n = t.arity();
            for (int i = 0; i < n; i++) {
                final Term sub = t.sub(i);
                final long sh;
                if (n > 4) {
                    // large arity: match recordWakeKeys' all-wildcard fallback exactly (else the
                    // base's specific key could never appear among the recorded keys -> a MISS)
                    sh = WILDCARD;
                } else if (sub.op() instanceof SchemaVariable ssv) {
                    final Object inst = insts.getInstantiation(ssv);
                    sh = (inst instanceof JTerm it)
                            ? structHash(stripUpdates(it), STRUCT_HASH_DEPTH)
                            : WILDCARD;
                } else {
                    // a concrete pattern sub may still hold schema variables -> wildcard
                    // (conservative: over-wakes, never misses)
                    sh = WILDCARD;
                }
                h = h * FNV_PRIME + sh;
            }
            keys.add(h);
        }
        return keys;
    }

    /**
     * Record the wake keys a changed formula produces: for the update-stripped formula of arity n,
     * all {@code 2^n} keys obtained by wildcarding each subset of its immediate sub-terms (so a
     * base
     * whose bound-sub pattern matches this formula finds its own key). Falls back to the
     * all-wildcard
     * (top-op) key for large arities.
     */
    private void recordWakeKeys(Term formula) {
        if (pendingWakeKeys == null) {
            pendingWakeKeys = new LinkedHashSet<>();
        }
        final Term t = stripUpdates(formula);
        final Operator top = t.op();
        final int n = t.arity();
        if (n > 4) {
            long h = top.hashCode();
            for (int i = 0; i < n; i++) {
                h = h * FNV_PRIME + WILDCARD;
            }
            pendingWakeKeys.add(h);
            return;
        }
        final long[] subHash = new long[n];
        for (int i = 0; i < n; i++) {
            subHash[i] = structHash(stripUpdates(t.sub(i)), STRUCT_HASH_DEPTH);
        }
        for (int mask = 0; mask < (1 << n); mask++) {
            long h = top.hashCode();
            for (int i = 0; i < n; i++) {
                final long sh = ((mask >> i) & 1) == 1 ? WILDCARD : subHash[i];
                h = h * FNV_PRIME + sh;
            }
            pendingWakeKeys.add(h);
        }
    }

    /**
     * Record, for the next round's wake-up, the wake key(s) of every formula added or modified by
     * this sequent change (fine: structural keys; coarse: top operators along the update-prefix
     * spine -- the assumes matcher strips the update context, so the spine is a sound superset).
     */
    private void recordWakeOps(ImmutableList<SequentFormula> added) {
        for (SequentFormula sf : added) {
            if (FINE_WAKE) {
                recordWakeKeys(sf.formula());
            } else {
                recordSpineOps(sf.formula());
            }
        }
    }

    private void recordModifiedWakeOps(ImmutableList<FormulaChangeInfo> modified) {
        for (FormulaChangeInfo fci : modified) {
            if (FINE_WAKE) {
                recordWakeKeys(fci.newFormula().formula());
            } else {
                recordSpineOps(fci.newFormula().formula());
            }
        }
    }

    /** Add the operators along a formula's update-application spine to {@link #pendingWakeOps}. */
    private void recordSpineOps(Term formula) {
        if (pendingWakeOps == null) {
            pendingWakeOps = new LinkedHashSet<>();
        }
        Term t = formula;
        while (true) {
            final Operator op = t.op();
            pendingWakeOps.add(op);
            if (op instanceof UpdateApplication && t instanceof JTerm jt) {
                t = UpdateApplication.getTarget(jt);
            } else {
                break;
            }
        }
    }

    /**
     * Deep-copy the (mutable, goal-local) parking structures into {@code target} so split goals
     * park/wake independently (contained containers and operators are immutable and shared).
     */
    private void copyParkingInto(EagerRuleApplicationManager target) {
        if (parkedByOp != null) {
            final LinkedHashMap<Operator, Collection<RuleAppContainer>> copy =
                new LinkedHashMap<>(parkedByOp.size());
            for (Map.Entry<Operator, Collection<RuleAppContainer>> e : parkedByOp.entrySet()) {
                final Collection<RuleAppContainer> v = e.getValue();
                copy.put(e.getKey(),
                    v instanceof LinkedHashSet ? new LinkedHashSet<>(v) : new ArrayList<>(v));
            }
            target.parkedByOp = copy;
        }
        if (pendingWakeOps != null) {
            target.pendingWakeOps = new LinkedHashSet<>(pendingWakeOps);
        }
        if (parkedByKey != null) {
            final LinkedHashMap<Long, Collection<RuleAppContainer>> copy =
                new LinkedHashMap<>(parkedByKey.size());
            for (Map.Entry<Long, Collection<RuleAppContainer>> e : parkedByKey.entrySet()) {
                final Collection<RuleAppContainer> v = e.getValue();
                copy.put(e.getKey(),
                    v instanceof LinkedHashSet ? new LinkedHashSet<>(v) : new ArrayList<>(v));
            }
            target.parkedByKey = copy;
        }
        if (pendingWakeKeys != null) {
            target.pendingWakeKeys = new LinkedHashSet<>(pendingWakeKeys);
        }
    }
}
