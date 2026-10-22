/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.match.vm.JavaMatchPlanBuilder;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;

import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.matcher.compiler.PatternKeySource;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/// After each change to the sequent the [QueueRuleApplicationManager] has to check whether
/// an incomplete taclet application due to missing matches of the `\\assumes` formula can be
/// completed.
/// To avoid re-matching all incomplete applications after each rule application, it parks them
/// using a so called _wake key_ built for each `\\assumes`-formula. Changed or new formulas are
/// matched cheaply against these keys. The applications parked under that key are then taken
/// (woken) to be matched fully against the new or changed formula.
///
/// The wake key for an `\\assumes`-formula is built from the top operator of the assumes formula
/// and (if it has one) from its first argument:
/// if the argument is concrete, the argument's top operator, otherwise if it is an already
/// instantiated schema variable the term itself.
///
/// If an assumes formula is only a simple schema variable (e.g., in case of the `replace_known`
/// taclets) two cases are distinguished:
/// 1. if the schema variable is instantiated then the instantiation is used as wake key
/// 2. otherwise, without an instantiation, no wake key can be constructed and such a taclet is
/// matched against after each rule application.
///
/// The exact wake key is computed using the actual taclet matcher
/// ([VMTacletMatcher#assumesKeySource]) and is a safe overapproximation, i.e., it is ensured
/// that no potential match is missed. Using the taclet matcher ensures consistency as there
/// is **no** duplicate matching logic.
///
/// The implementation is defensive to avoid that a match is missed, i.e., the applications parked
/// under a wake key are always woken, if a match might be possible. Applications that have been
/// woken, but whose full match is unsuccessful, are parked again. The defensiveness extends to the
/// implementation of [VMTacletMatcher#assumesKeySource], if this returns
/// [PatternKeySource.Unkeyable], then the corresponding taclet applications are matched against at
/// every step and the only consequence is a performance regression.
///
/// In summary: A key describes a potential match by its operator family or by the formula up to
/// renaming.
/// A modified sequent formula wakes the candidates parked under the keys of the formula below
/// its leading updates. Keys are equal if their operator families are identical and their
/// terms are equal up to renaming ([TermModRenaming]). A modality top operator has no
/// term key for performance reasons (its program would be hashed at every proof step).
///
/// After changing anything in this class: RunAllProofs and a run without parking **must**
/// be run before committing/pushing. Map, buckets and pending set are insertion-ordered, so the
/// wake order is the same in every run.
///
@NullMarked
final class ParkedBases {

    /// The parked rule application containers (bases), grouped by their wake key.
    /// A bucket is a plain [ArrayList] while small: a base is parked at most once per bucket
    /// and bases compare by object identity, so there is nothing to de-duplicate and a set would
    /// waste memory. If the size of a bucket becomes greater than or equal to
    /// [#BUCKET_SET_THRESHOLD],
    /// a [LinkedHashSet] is used instead of the [ArrayList] to keep removing a woken
    /// base by value at amortized constant time (see [#park]).
    private @Nullable LinkedHashMap<WakeKey, Collection<RuleAppContainer>> parked = null;

    /// Bucket size at which a parking bucket is promoted from ArrayList to LinkedHashSet.
    private static final int BUCKET_SET_THRESHOLD = 16;

    /// The [WakeKey]s of every formula that was added to or changed in the sequent since the
    /// previous rule application. [#getAndClearWokenApplications()] reads and then empties
    /// this set at the start of the next round to decide which parked bases to wake.
    /// `null` until the first change is recorded. Package-private for the unit tests in
    /// this package.
    @Nullable
    LinkedHashSet<WakeKey> pendingWakeKeys = null;

    /// Number of [#park] calls since the last [#sweepDeadParkedBases], and the
    /// number of parked containers that survived that sweep. Together they trigger the next
    /// sweep: both counters depend only on this goal's own history, so the sweep runs at the
    /// same point in every run.
    private int parksSinceSweep = 0;
    private int survivorsAtLastSweep = 0;

    /// Number of parked taclet applications of the parked map per key head and [WakeKind]:
    /// the array under a head holds one count per kind, indexed by its ordinal.
    /// [#recordWakeKeysOf] skips every key whose head and kind have no parked base, and
    /// in particular computes no hash then. The map is only queried by key, never iterated in a
    /// way the proof could observe, so a plain [HashMap] is safe here. Kept up to date
    /// by [#park], [#unindexParked], and [#sweepDeadParkedBases].
    private final HashMap<Object, int[]> parkedCountsByHead = new HashMap<>();

    /// Number of [WakeKind]s, the length of the count arrays above.
    private static final int KINDS = WakeKind.values().length;

    /// Minimum number of parks before the first sweep, so small proofs never sweep.
    private static final int SWEEP_FLOOR = 64;


    /// The wake kind describes the structure of the wake key and with that its precision. Below,
    /// _core_ means the formula after its update chain has been removed, and
    /// _descriptor_ refers to an operator family as defined by the matcher
    /// ([JavaMatchPlanBuilder#matchFamilyOf] for concrete operators,
    /// [org.key_project.prover.rules.matcher.compiler.PatternKeySource] for patterns).
    enum WakeKind {
        /// the key uses only the operator family of the top level operator;
        /// the [WakeKey#datum] field of the key has no meaning when this kind applies.
        OP,
        /// In addition to the operator family of the top level operator, the key also contains the
        /// operator family of the top operator's first argument in [WakeKey#datum].
        ARG_OP,
        /// In addition to the operator family of the top level operator, the key contains the first
        /// argument as term (compared up to renaming), as a [TermModRenaming] in
        /// [WakeKey#datum].
        ARG_HASH,
        /// In addition to the operator family of the top level operator, the key contains the whole
        /// formula as a [TermModRenaming] in [WakeKey#datum] (this is the case if the
        /// `\\assumes`-formula is a simple schema variable with an instantiation).
        WHOLE_HASH
    }

    /// The actual wake key. Argument `kind` describes the precision of the key,
    /// `inAntecedent` describes whether the assumes formula occurs in the antecedent or
    /// succedent, the descriptor `head` of the (core) formula's top operator (its operator
    /// family, see above), and `datum` holds one extra value whose meaning depends on the kind
    /// (see [WakeKind]).
    ///
    /// A parked base is stored under the most precise key its
    /// `\assumes` shape allows ([#parkKeys]). All possible keys for a new or changed
    /// formula are built in [#recordWakeKeysOf] such that a parked rule application is woken
    /// exactly when a new or changed formula produces a key equal to one the base is stored under.
    ///
    /// Note: If the class gets refactored and tested again (please use differential testing),
    /// this record can be made more type safe by a sealed interface.
    record WakeKey(WakeKind kind, boolean inAntecedent, Object head, @Nullable Object datum) {
    }

    /// A simple term wrapper to ensure that terms are compared modulo renaming as used by the
    /// taclet matcher.
    /// The parked map thus finds the bucket by the hash and decides by the equality, so the hash
    /// function has no influence on which bases are woken. An earlier attempt used just the
    /// hashcode (without the equality check), but this leads to non-deterministic cost assignments
    /// as the age of woken rule applications is modified.
    record TermModRenaming(JTerm term) {
        @Override
        public boolean equals(@Nullable Object o) {
            return o instanceof TermModRenaming other
                    && term.equalsModProperty(other.term, RENAMING_TERM_PROPERTY);
        }

        @Override
        public int hashCode() {
            return term.hashCodeModRenaming();
        }
    }

    /// The order in which [#getAndClearWokenApplications()] collects woken bases across the
    /// four kinds.
    /// Bases are put back into the queue in the order they are collected, and that order decides
    /// how the queue arranges candidates of equal cost, so it must stay fixed for the proof to stay
    /// the same.
    private static final WakeKind[] WAKE_ORDER =
        { WakeKind.OP, WakeKind.ARG_HASH, WakeKind.ARG_OP, WakeKind.WHOLE_HASH };
    static {
        // A kind missing here would never wake its bases; the proof-relevant property of the
        // order itself is only that it is fixed.
        assert new HashSet<>(Arrays.asList(WAKE_ORDER)).size() == WakeKind.values().length
                : "WAKE_ORDER must list every WakeKind exactly once";
    }

    /// Creates and returns the wake keys (here, also referred to as park keys as they are
    /// constructed for the `\\assumes`-formula) under which the given taclet application is
    /// stored in the parked map.
    /// Returns `null` when the base cannot be parked at all, for example, if an
    /// `\assumes` top operator is a not yet instantiated schema variable. If the top
    /// level operator of the formula is a modality, a rather imprecise key only specifying the
    /// operator family (e.g. `Modality.Kind`) of kind [WakeKind#OP] is returned;
    /// for performance reasons.
    ///
    /// The method does not inspect and extract the key components itself but refers to the taclet's
    /// matcher ([VMTacletMatcher#assumesKeySource]) to avoid duplication of matching logic,
    /// thus maintaining consistency.
    /// This method only combines those summaries with the main match's instantiations, and picks
    /// the most precise [WakeKind] they allow.
    ///
    /// Note: Precise keys are only computed for taclets with exactly one `\\assumes`-formula.
    /// Potential for future improvements.
    ///
    /// @param app the taclet application for whose `\\assumes`-formulas wake keys are retrieved
    /// @return null if the taclet application cannot be parked and has to be matched after each
    /// change to a sequent;
    /// otherwise it contains for each `\\assumes`-formula a wake key (if several formulas
    /// share the same key only one key exists, hence, `\\result.size()` might
    /// be less than the number of `\\assumes`-formulas)
    static @Nullable List<WakeKey> parkKeys(NoPosTacletApp app) {
        if (!(app.taclet().getMatcher() instanceof VMTacletMatcher matcher)) {
            return null;
        }
        final Sequent assumesSeq = app.taclet().assumesSequent();
        if (assumesSeq.size() == 1) {
            final boolean inAntec = !assumesSeq.antecedent().isEmpty();
            final Term pattern =
                assumesSeq.iterator().next().formula();
            final PatternKeySource source = matcher.assumesKeySource(pattern);
            if (source instanceof PatternKeySource.ByWholeSchemaVariable whole) {
                if (app.instantiations().getInstantiation(whole.sv()) instanceof JTerm instTerm) {
                    // the main match fixed the whole assumes formula (rules replace_known_* and
                    // close); key on the hash of its core, the same form the wake side hashes
                    JTerm core = instTerm;
                    while (core.op() instanceof UpdateApplication) {
                        core = UpdateApplication.getTarget(core);
                    }
                    final Object head = JavaMatchPlanBuilder.matchFamilyOf(core.op());
                    if (head != null && !(core.op() instanceof JModality)) {
                        return List.of(new WakeKey(WakeKind.WHOLE_HASH, inAntec, head,
                            new TermModRenaming(core)));
                    }
                }
            } else if (source instanceof PatternKeySource.ByHead byHead
                    && !(byHead.headDescriptor() instanceof Modality.Kind)) {
                if (byHead
                        .firstArg() instanceof PatternKeySource.FirstArg.ByArgSchemaVariable argSv) {
                    if (app.instantiations()
                            .getInstantiation(argSv.sv()) instanceof JTerm instTerm
                            && !(instTerm.op() instanceof JModality)) {
                        // the main match fixed the assumes first argument (the applyEq family:
                        // \assumes(s = t1) with s already bound to the term being rewritten)
                        return List.of(new WakeKey(WakeKind.ARG_HASH, inAntec,
                            byHead.headDescriptor(), new TermModRenaming(instTerm)));
                    }
                } else if (byHead
                        .firstArg() instanceof PatternKeySource.FirstArg.ByArgHead argHead) {
                    // the assumes first argument is itself a term with a fixed top operator
                    // (for example \assumes(store(h, o, f1, x) = EQ))
                    return List.of(new WakeKey(WakeKind.ARG_OP, inAntec,
                        byHead.headDescriptor(), argHead.descriptor()));
                }
            }
        }
        return assumesOpKeys(app, matcher);
    }

    /// Computes for each `\\assumes`-formula of the provided taclet application the coarse wake key
    /// of kind [WakeKind#OP].
    ///
    /// @param app the taclet application for which to compute the wake keys
    /// @param matcher the [VMTacletMatcher] to use for constructing the keys' components
    private static @Nullable List<WakeKey> assumesOpKeys(NoPosTacletApp app,
            VMTacletMatcher matcher) {
        final Sequent assumesSeq = app.taclet().assumesSequent();
        if (assumesSeq.isEmpty()) {
            return null;
        }
        // one key per distinct family and side: several assumes formulas may share a top
        // operator, and a base must be stored at most once per bucket
        final LinkedHashSet<WakeKey> keys = new LinkedHashSet<>(assumesSeq.size());
        for (int side = 0; side < 2; side++) {
            final boolean inAntec = side == 0;
            for (SequentFormula sf : inAntec ? assumesSeq.antecedent() : assumesSeq.succedent()) {
                final PatternKeySource source = matcher.assumesKeySource(sf.formula());
                final Object head;
                if (source instanceof PatternKeySource.ByHead byHead) {
                    head = byHead.headDescriptor();
                } else if (source instanceof PatternKeySource.ByWholeSchemaVariable whole
                        && app.instantiations()
                                .getInstantiation(whole.sv()) instanceof JTerm instTerm) {
                    // This keys a top position, which the wake side observes with leading
                    // updates stripped, so an update-headed instantiation has no key a wake
                    // could meet. Such a base is left unparked rather than stripped here,
                    // because parking it changes which candidates carry their parked cost.
                    head = instTerm.op() instanceof UpdateApplication ? null
                            : JavaMatchPlanBuilder.matchFamilyOf(instTerm.op());
                } else {
                    head = null;
                }
                if (head == null) {
                    return null;
                }
                keys.add(new WakeKey(WakeKind.OP, inAntec, head, null));
            }
        }
        return List.copyOf(keys);
    }

    /// Park the given taclet application container, under each of its [#parkKeys].
    ///
    /// @param base the re-costed base container to park (carries the current age)
    /// @param goal the goal the base belongs to, used by the dead-base sweep
    /// @return `true` if the base was parked, `false` if it cannot be parked (see
    /// [#parkKeys]) and the caller must keep it in the queue
    boolean park(TacletAppContainer base, @Nullable Goal goal) {
        final List<WakeKey> keys = parkKeys(base.getTacletApp());
        if (keys == null) {
            return false;
        }
        if (parked == null) {
            parked = new LinkedHashMap<>();
        }
        for (WakeKey key : keys) {
            final Collection<RuleAppContainer> bucket =
                parked.computeIfAbsent(key, k -> new ArrayList<>(4));
            bucket.add(base);
            parkedCountsByHead.computeIfAbsent(key.head(), h -> new int[KINDS])[key.kind()
                    .ordinal()]++;
            if (bucket.size() == BUCKET_SET_THRESHOLD && bucket instanceof ArrayList) {
                parked.put(key, new LinkedHashSet<>(bucket));
            }
        }
        parksSinceSweep++;
        if (parksSinceSweep >= survivorsAtLastSweep + SWEEP_FLOOR) {
            sweepDeadParkedBases(goal);
        }
        return true;
    }

    /// Remove every parked base that can no longer be applied because its find position
    /// (the term it matched against) disappeared from the sequent (the same test,
    /// [TacletAppContainer#isStillApplicable], that would drop the base if it were woken).
    /// Such bases would otherwise stay parked until their key happens to fire, holding on to their
    /// rule application and the old formulas it points to.
    ///
    /// The sweep runs from [#park] once the number of parks since the last sweep
    /// reaches the number of survivors of that sweep (plus a floor for small proofs), so it walks
    /// the whole map at most once per doubling: the cost per park is constant on average, and the
    /// map never holds more than about twice the still-applicable bases. Removal keeps the
    /// insertion order of the surviving entries, and the trigger depends only on this goal's own
    /// park history, so the sweep does not introduce run-to-run differences.
    private void sweepDeadParkedBases(@Nullable Goal goal) {
        if (parked == null || goal == null) {
            return;
        }
        assert parkedCountsConsistent() : "parkedCountsByHead out of step with the parked map";
        parksSinceSweep = 0;
        survivorsAtLastSweep = 0;
        final Goal g = goal;
        // the sweep walks every entry anyway, so the counts are recomputed from scratch
        // instead of tracking each removal
        parkedCountsByHead.clear();
        final var entries = parked.entrySet().iterator();
        while (entries.hasNext()) {
            final var entry = entries.next();
            final Collection<RuleAppContainer> bucket = entry.getValue();
            bucket.removeIf(c -> c instanceof TacletAppContainer tac && !tac.isStillApplicable(g));
            if (bucket.isEmpty()) {
                entries.remove();
            } else {
                survivorsAtLastSweep += bucket.size();
                final WakeKey key = entry.getKey();
                parkedCountsByHead.computeIfAbsent(key.head(), h -> new int[KINDS])[key.kind()
                        .ordinal()] += bucket.size();
            }
        }
    }

    /// Changes to the sequent trigger a call to [#recordWakeKeysOf(Term, boolean)] which
    /// collects the wake keys under which potentially matchable taclet applications are parked in
    /// [#pendingWakeKeys]. The woken applications are removed from the parking map and may
    /// need to be explicitly reparked if not completed.
    ///
    /// This method collects the taclet applications parked under these keys and clears the pending
    /// wake keys set. For determinism, the apps are collected in a fixed order determined by the
    /// one given in [#WAKE_ORDER].
    ///
    /// @return the woken applications in wake order; empty if nothing is to be woken
    Collection<RuleAppContainer> getAndClearWokenApplications() {
        if (pendingWakeKeys == null) {
            return List.of();
        }
        LinkedHashSet<RuleAppContainer> woken = null;
        if (parked != null && !parked.isEmpty()) {
            for (WakeKind kind : WAKE_ORDER) {
                for (WakeKey key : pendingWakeKeys) {
                    if (key.kind() != kind) {
                        continue;
                    }
                    final Collection<RuleAppContainer> bucket = parked.get(key);
                    if (bucket != null) {
                        if (woken == null) {
                            woken = new LinkedHashSet<>();
                        }
                        woken.addAll(bucket);
                    }
                }
            }
        }
        pendingWakeKeys.clear();
        if (woken == null) {
            return List.of();
        }
        for (RuleAppContainer c : woken) {
            unindexParked(c);
        }
        return woken;
    }

    /// Remove a base that is being woken from every bucket that holds it.
    private void unindexParked(RuleAppContainer c) {
        if (parked == null || !(c instanceof TacletAppContainer tac)) {
            return;
        }

        /*
         * The keys are recomputed by {@link #parkKeys}; this yields the keys the base was stored
         * under, because everything they are computed from (the taclet, its instantiations,
         * the cached hashes) is never modified after the base was parked. A failed removal would
         * mean this assumption broke and the taclet application would stay in the map forever.
         * We check this assumption with the asserts to fail fast in case of a bug.
         */
        final List<WakeKey> keys = parkKeys(tac.getTacletApp());
        if (keys == null) {
            return;
        }
        for (WakeKey key : keys) {
            final Collection<RuleAppContainer> bucket = parked.get(key);
            assert bucket != null : "woken base has no bucket under its park key";
            if (bucket != null) {
                final boolean removed = bucket.remove(c);
                assert removed : "woken base was not stored in its park bucket";
                if (removed) {
                    final int[] counts = parkedCountsByHead.get(key.head());
                    if (counts != null && --counts[key.kind().ordinal()] == 0
                            && Arrays.stream(counts).allMatch(n -> n == 0)) {
                        parkedCountsByHead.remove(key.head());
                    }
                }
                if (bucket.isEmpty()) {
                    parked.remove(key);
                }
            }
        }
    }

    /// Computes the wake keys for a new or modified sequent formula used to lookup (wake) potential
    /// matching parked taclet applications.
    ///
    /// The computed keys are stored in [#pendingWakeKeys]. This is the wake counterpart of
    /// [#parkKeys]: the two produce the same kinds of keys, so a base is woken exactly when a
    /// changed formula could match it.
    ///
    /// @param formula the changed sequent formula for which to produce wake keys
    /// @param inAntecedent true if the formula occurs in the antecedent, false if it occurs
    /// in the succedent
    void recordWakeKeysOf(Term formula, boolean inAntecedent) {
        // The return early tests like the one below rest on the
        // fact that it is always established that parking happens
        // before any change is reported and the corresponding wake
        // keys are determined.
        if (parked == null || parked.isEmpty()) {
            // no parked apps no need to check if we can wake anything
            return;
        }
        // Strip the leading updates the matcher would strip before matching, so both sides key
        // on the same core; only the top position is observed stripped, an update application
        // at the core's first argument keeps its own family below.
        Term t = formula;
        while (t.op() instanceof UpdateApplication && t instanceof JTerm jt) {
            t = UpdateApplication.getTarget(jt);
        }
        final Object head = JavaMatchPlanBuilder.matchFamilyOf(t.op());
        if (head == null) {
            return;
        }
        final int[] counts = parkedCountsByHead.get(head);
        if (counts == null) {
            // all wake keys have a head, if there is no parked app with a matching head there is
            // nothing to do
            return;
        }
        if (pendingWakeKeys == null) {
            pendingWakeKeys = new LinkedHashSet<>();
        }
        if (counts[WakeKind.OP.ordinal()] > 0) {
            pendingWakeKeys.add(new WakeKey(WakeKind.OP, inAntecedent, head, null));
        }
        if (head instanceof Modality.Kind) {
            // no hash keys exist for modality formulas (see parkKeys), so nothing else to do
            return;
        }
        if (t instanceof JTerm core) {
            if (counts[WakeKind.WHOLE_HASH.ordinal()] > 0) {
                pendingWakeKeys.add(new WakeKey(WakeKind.WHOLE_HASH, inAntecedent, head,
                    new TermModRenaming(core)));
            }
            if (core.arity() > 0 && core.sub(0) instanceof JTerm firstArg) {
                if (counts[WakeKind.ARG_OP.ordinal()] > 0) {
                    final Object argHead = JavaMatchPlanBuilder.matchFamilyOf(firstArg.op());
                    if (argHead != null) {
                        pendingWakeKeys.add(
                            new WakeKey(WakeKind.ARG_OP, inAntecedent, head, argHead));
                    }
                }
                if (counts[WakeKind.ARG_HASH.ordinal()] > 0
                        && !(firstArg.op() instanceof JModality)) {
                    pendingWakeKeys.add(new WakeKey(WakeKind.ARG_HASH, inAntecedent, head,
                        new TermModRenaming(firstArg)));
                }
            }
        }
    }

    /// A deep copy for a goal that splits into two: fresh map, fresh buckets, fresh pending set,
    /// so the two goals park and wake independently (see the copy method of
    /// [QueueRuleApplicationManager] for why sharing would change proofs). The stored
    /// containers and the key components are never modified in place and stay shared. The copy
    /// starts with the same parked population, so it inherits the sweep counters.
    ParkedBases copy() {
        final ParkedBases res = new ParkedBases();
        if (parked != null) {
            final LinkedHashMap<WakeKey, Collection<RuleAppContainer>> copy =
                new LinkedHashMap<>(parked.size());
            for (var e : parked.entrySet()) {
                final Collection<RuleAppContainer> v = e.getValue();
                copy.put(e.getKey(),
                    v instanceof LinkedHashSet ? new LinkedHashSet<>(v) : new ArrayList<>(v));
            }
            res.parked = copy;
        }
        if (pendingWakeKeys != null) {
            res.pendingWakeKeys = new LinkedHashSet<>(pendingWakeKeys);
        }
        res.parksSinceSweep = parksSinceSweep;
        res.survivorsAtLastSweep = survivorsAtLastSweep;
        for (var e : parkedCountsByHead.entrySet()) {
            res.parkedCountsByHead.put(e.getKey(), e.getValue().clone());
        }
        return res;
    }

    /// Consistency of [#parkedCountsByHead] with the parked map, for asserts.
    private boolean parkedCountsConsistent() {
        final HashMap<Object, int[]> expected = new HashMap<>();
        if (parked != null) {
            for (var e : parked.entrySet()) {
                final WakeKey key = e.getKey();
                expected.computeIfAbsent(key.head(), h -> new int[KINDS])[key.kind().ordinal()] +=
                    e.getValue().size();
            }
        }
        if (!expected.keySet().equals(parkedCountsByHead.keySet())) {
            return false;
        }
        for (var e : expected.entrySet()) {
            if (!Arrays.equals(e.getValue(), parkedCountsByHead.get(e.getKey()))) {
                return false;
            }
        }
        return true;
    }

    /// Access to the parked map for the deep-copy test in this package.
    @Nullable
    LinkedHashMap<WakeKey, Collection<RuleAppContainer>> parkedMapForTests() {
        return parked;
    }

    /// Insert an entry under the given key, bypassing [#parkKeys]; only for tests.
    void parkForTests(WakeKey key, RuleAppContainer entry) {
        if (parked == null) {
            parked = new LinkedHashMap<>();
        }
        parked.computeIfAbsent(key, k -> new ArrayList<>(4)).add(entry);
        parkedCountsByHead.computeIfAbsent(key.head(), h -> new int[KINDS])[key.kind().ordinal()]++;
    }
}
