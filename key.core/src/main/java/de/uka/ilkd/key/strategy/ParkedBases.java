/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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

/**
 * Candidates of a {@link QueueRuleApplicationManager} that are currently set aside, grouped by
 * the formula they are waiting for.
 *
 * <p>
 * Some vocabulary. A rule of KeY is called a <em>taclet</em>. A taclet may carry an
 * {@code \assumes} part: one or more formulas that must already be present in the sequent for
 * the rule to be applicable. A candidate whose {@code \assumes} formula is not present yet is
 * called a <em>base</em> here: it cannot be applied now, but it may become applicable in a
 * later round once such a formula appears. Deciding a taclet's applicability means
 * <em>matching</em> its formulas against the sequent, where a schema variable in the taclet
 * (a placeholder) stands for an arbitrary concrete term. Matching a taclet against the whole
 * sequent every round is the expensive operation this class avoids.
 *
 * <p>
 * Measurements on a large proof: almost every candidate returned by the queue is a base whose
 * {@code \assumes} still does not match (about 96.8%), and re-matching it almost never
 * produces a new applicable rule (about 97 to 99.6% of the time it produces nothing). So
 * instead of returning such a base every round only to match and discard it, it is held back.
 * Setting a base aside is called <em>parking</em> it ({@link #park}); putting it back into the
 * queue is called <em>waking</em> it. A parked base is stored under one or more {@link WakeKey}s
 * that describe the formula it is waiting for ({@link #parkKeys}), and is woken as soon as a
 * formula matching such a key is added to or changed in the sequent
 * ({@link #recordWakeKeysOf}, {@link #drainWoken}).
 *
 * <p>
 * This is intended to find the same proof as returning every base every round. A base that
 * is woken too eagerly does no harm: it is returned, fails to match, and is parked again,
 * exactly as an un-parked base would have behaved that round. A base that is woken too late
 * would change the proof, because the rule application it produces would be created, and so
 * aged (see the comment on {@link QueueRuleApplicationManager}), in a later round. The
 * following points show that a wake is never late.
 * <ul>
 * <li>A base is parked only if the top operator (the outermost function or connective) of each
 * of its {@code \assumes} formulas is either concrete or a schema variable that the rule's
 * main match already fixed to a concrete term (see {@link #parkKeys}). If some top operator is
 * an unfixed schema variable, the formula would match anything, so the base is not parked and
 * stays in the queue as before. What a pattern could accept is stated by the taclet's own
 * matcher ({@link VMTacletMatcher#assumesKeySource}), derived from the same dispatch its
 * matching is built from, so park keys and matching cannot drift apart.</li>
 * <li>A parked base is woken in exactly the round in which a formula it could match is added
 * or changed. That is the same round in which an un-parked copy would first see that formula
 * as new and become applicable. So the resulting rule application is created in the same round
 * either way, with the same age and cost.</li>
 * <li>A formula may be wrapped in a chain of <em>updates</em> (an update is a pending
 * assignment written in front of a formula, as in {@code {x := 1} phi}). The matcher removes
 * this update chain before it matches. The keys of kind {@link WakeKind#OP} therefore use the
 * top operator of the formula and of every formula obtained by removing one update from the
 * front, which is a safe over-approximation of what the matcher could accept.</li>
 * <li>The other three key kinds filter more precisely, using only conditions the matcher
 * checks literally. A base whose {@code \assumes} first argument is a concrete term can only
 * match a formula whose first argument has the same top operator ({@link WakeKind#ARG_OP}). A
 * base whose {@code \assumes} first argument (or whole formula) was fixed to a concrete term
 * by the main match can only match a formula equal to it up to renaming of bound variables,
 * and equal terms up to that renaming have the same {@link JTerm#hashCodeModRenaming()}, so
 * filtering by that hash ({@link WakeKind#ARG_HASH}, {@link WakeKind#WHOLE_HASH}) never drops
 * a formula the matcher would accept. Parking and waking hash the formula after its update
 * chain has been removed, so the two sides compare the same thing.</li>
 * <li>No hash is ever computed over a term whose top operator is a modality (a program
 * nested deeper is still hashed; the guard is by the top operator). Such a term
 * carries a program, and its hash walks that whole program; in a proof that executes a large
 * program step by step, the changed formula is a fresh term every step, so nothing is cached
 * and the walks add up to time quadratic in the program size. A base waiting for such a
 * formula is parked under the coarse {@link WakeKind#OP} key of the modality kind instead
 * ({@link #parkKeys}), and the wake side then stops at that key for modality formulas
 * ({@link #recordWakeKeysOf}). The base is woken whenever any formula of that kind changes,
 * which is more often than the exact hash would wake it, and that is harmless (see
 * above).</li>
 * </ul>
 * <p>
 * One assumption remains. A parked container keeps the cost it was parked with, while an
 * un-parked base is re-costed with a fresh age share every time the queue returns it. The
 * two runs still perform the same proof steps as long as, in every round and in both runs,
 * all candidates cheaper than the rule application the round finally selects are processed
 * in that round. Every measurement so far satisfies this (statistics-identical benchmark
 * runs and the RunAllProofs suite), but it is an assumption about the costs the strategy
 * produces, not a proven theorem. A statistics comparison against a run without parking and
 * a RunAllProofs run are therefore mandatory when changing anything in this area.
 * <p>
 * Three implementation notes. The map, its buckets, and {@link #pendingWakeKeys} must stay
 * insertion-ordered: the hash codes of operators differ from run to run, so iterating a
 * plain hash-ordered container would make the wake order, and with it the proof, differ from
 * run to run. A parked base whose find position has meanwhile disappeared from the
 * sequent is not removed at that moment; it is removed by {@link #sweepDeadParkedBases},
 * which keeps the memory held by such bases bounded (see there). Waking such a base is also
 * harmless: its re-expansion notices that it is no longer applicable and drops it. And a
 * changed formula only produces keys under whose head and kind some base is currently
 * parked (see {@link #recordWakeKeysOf} for why no wake can be missed); without this filter,
 * every change of a possibly very large formula would compute the two hashes, which walk
 * the whole formula, even in a proof that parks nothing or parks nothing with that head.
 */
@NullMarked
final class ParkedBases {
    /**
     * The parked bases, grouped by the key of the formula they wait for. A bucket is a plain
     * {@link ArrayList} while small: a base is parked at most once per bucket and bases compare
     * by object identity, so there is nothing to de-duplicate and a set would waste memory. A
     * bucket past {@link #BUCKET_SET_THRESHOLD} becomes a {@link LinkedHashSet} to keep removing
     * a woken base by value constant time (see {@link #park}).
     */
    private @Nullable LinkedHashMap<WakeKey, Collection<RuleAppContainer>> parked = null;

    /**
     * Bucket size at which a parking bucket is promoted from ArrayList to LinkedHashSet.
     */
    private static final int BUCKET_SET_THRESHOLD = 16;

    /**
     * The {@link WakeKey}s of every formula that was added to or changed in the sequent since the
     * previous round. {@link #drainWoken()} reads and then empties this set at the start of
     * the next round to decide which parked bases to wake. {@code null} until the first change is
     * recorded. Package-private for the unit tests in this package.
     */
    @Nullable
    LinkedHashSet<WakeKey> pendingWakeKeys = null;

    /**
     * Number of {@link #park} calls since the last {@link #sweepDeadParkedBases}, and the
     * number of parked containers that survived that sweep. Together they trigger the next
     * sweep: both counters depend only on this goal's own history, so the sweep runs at the
     * same point in every run.
     */
    private int parksSinceSweep = 0;
    private int survivorsAtLastSweep = 0;

    /**
     * Number of entries of the parked map per key head and {@link WakeKind}: the array under a
     * head holds one count per kind, indexed by its ordinal. {@link #recordWakeKeysOf} skips
     * every key whose head and kind have no parked base, and in particular computes no hash
     * then; see there for why this cannot suppress a needed wake. The map is only queried by
     * key, never iterated in a way the proof could observe, so a plain {@link HashMap} is safe
     * here. Kept up to date by {@link #park}, {@link #unindexParked}, and
     * {@link #sweepDeadParkedBases}.
     */
    private final HashMap<Object, int[]> parkedCountsByHead = new HashMap<>();

    /** Number of {@link WakeKind}s, the length of the count arrays above. */
    private static final int KINDS = WakeKind.values().length;

    /** Minimum number of parks before the first sweep, so small proofs never sweep. */
    private static final int SWEEP_FLOOR = 64;

    /**
     * How precisely a {@link WakeKey} describes the formula a parked base waits for. Below,
     * <em>core</em> means the formula after its update chain has been removed (see the class
     * comment), and <em>descriptor</em> refers to an operator family as defined by the matcher
     * ({@link JavaMatchPlanBuilder#matchFamilyOf} for concrete operators,
     * {@link org.key_project.prover.rules.matcher.compiler.PatternKeySource} for patterns).
     */
    enum WakeKind {
        /** The extra value is absent; the key uses only a descriptor of a top operator. */
        OP,
        /** The extra value is the descriptor of the core's first argument's top operator. */
        ARG_OP,
        /** The extra value is {@link JTerm#hashCodeModRenaming()} of the core's first argument. */
        ARG_HASH,
        /** The extra value is {@link JTerm#hashCodeModRenaming()} of the whole core. */
        WHOLE_HASH
    }

    /**
     * One entry key of the parked map. It holds the precision {@code kind}, the side of the
     * sequent the formula is expected on ({@code inAntecedent}; an {@code \assumes} formula is
     * only ever matched against formulas of its own side, so keys of different sides never
     * meet), the descriptor {@code head} of the (core) formula's top operator (its operator
     * family, see above), and one
     * extra value whose meaning depends on the kind (see {@link WakeKind}): {@code null} for
     * {@link WakeKind#OP}, a descriptor for {@link WakeKind#ARG_OP}, an {@link Integer} hash for
     * the two hash kinds. A parked base is stored under the most precise key its {@code \assumes}
     * shape allows ({@link #parkKeys}). A changed formula produces every key a base could match
     * it with ({@link #recordWakeKeysOf}). A base is therefore woken exactly when some changed
     * formula produces a key equal to one the base is stored under.
     */
    record WakeKey(WakeKind kind, boolean inAntecedent, Object head, @Nullable Object datum) {
    }

    /**
     * The order in which {@link #drainWoken()} collects woken bases across the four kinds.
     * Bases are put back into the queue in the order they are collected, and that order decides
     * how the queue arranges candidates of equal cost, so it must stay fixed for the proof to stay
     * the same.
     */
    private static final WakeKind[] WAKE_ORDER =
        { WakeKind.OP, WakeKind.ARG_HASH, WakeKind.ARG_OP, WakeKind.WHOLE_HASH };
    static {
        // A kind missing here would never wake its bases; the proof-relevant property of the
        // order itself is only that it is fixed.
        assert new HashSet<>(Arrays.asList(WAKE_ORDER)).size() == WakeKind.values().length
                : "WAKE_ORDER must list every WakeKind exactly once";
    }

    /**
     * The keys under which the given base is stored in the parked map: a single precise key when
     * the shape of the base's {@code \assumes} allows one, otherwise one {@link WakeKind#OP} key
     * per {@code \assumes} formula. Returns {@code null} when the base cannot be parked at all,
     * that is when some {@code \assumes} top operator is a schema variable the main match did not
     * fix to a concrete term; such a base stays in the queue. A base whose formula or hashed
     * term has a modality at the top gets no precise key and falls through to the coarse
     * {@link WakeKind#OP} case; see the class comment for why modality terms are never hashed.
     * <p>
     * What each {@code \assumes} pattern could accept is not analyzed here: the taclet's matcher
     * summarizes each of its assumes formulas ({@link VMTacletMatcher#assumesKeySource}), derived
     * from the same per-operator dispatch its matching is built from, so the keys cannot drift
     * from what the matcher accepts. This method only combines those summaries with the main
     * match's instantiations, and picks the most precise {@link WakeKind} they allow.
     */
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
                            core.hashCodeModRenaming()));
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
                            byHead.headDescriptor(), instTerm.hashCodeModRenaming()));
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

    /**
     * One {@link WakeKind#OP} key per {@code \assumes} formula of the given taclet application,
     * on the formula's own side of the sequent: the key's family comes from the formula's key
     * source, or, for a schema-variable top, from the operator the main match fixed it to.
     * Returns {@code null} if the application has no {@code \assumes} formulas, or if some
     * formula yields no family (an unfixed schema variable would match anything; an update
     * application or a schematic modality kind cannot be keyed). Used for a base that none of
     * the precise cases in {@link #parkKeys} apply to.
     */
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

    /**
     * Set the given base aside, under each of its {@link #parkKeys}.
     *
     * @param base the re-costed base container to park (carries the current age)
     * @param goal the goal the base belongs to, used by the dead-base sweep
     * @return {@code true} if the base was parked, {@code false} if it cannot be parked (see
     *         {@link #parkKeys}) and the caller must keep it in the queue
     */
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

    /**
     * Remove every parked base that can no longer be applied because its find position has
     * disappeared from the sequent (the same test, {@link TacletAppContainer#isStillApplicable},
     * that would drop the base if it were woken). Such bases would otherwise stay parked until
     * their key happens to fire, holding on to their rule application and the old formulas it
     * points to. The sweep runs from {@link #park} once the number of parks since the last sweep
     * reaches the number of survivors of that sweep (plus a floor for small proofs), so it walks
     * the whole map at most once per doubling: the cost per park is constant on average, and the
     * map never holds more than about twice the still-applicable bases. Removal keeps the
     * insertion order of the surviving entries, and the trigger depends only on this goal's own
     * park history, so the sweep does not introduce run-to-run differences.
     */
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

    /**
     * The parked bases that some formula changed since the previous round could match (see
     * {@link #pendingWakeKeys}); the caller puts them back into the queue. Bases are collected
     * one {@link WakeKind} at a time in {@link #WAKE_ORDER}, within a kind in the order the
     * changes were recorded, and each collected base is removed from the parked map. Empties
     * the pending change set.
     *
     * @return the woken bases in wake order; empty if nothing is to be woken
     */
    Collection<RuleAppContainer> drainWoken() {
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

    /**
     * Remove a base that is being woken from every bucket that holds it. The keys are recomputed
     * by {@link #parkKeys}; this yields the keys the base was stored under, because everything
     * they are computed from (the taclet, its instantiations, the cached hashes) is never
     * modified after the base was parked. A failed removal would mean this assumption broke and
     * the base would stay in the map forever, hence the asserts.
     */
    private void unindexParked(RuleAppContainer c) {
        if (parked == null || !(c instanceof TacletAppContainer tac)) {
            return;
        }
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

    /**
     * Add to {@link #pendingWakeKeys} every {@link WakeKey} that the given formula could let a
     * parked base match. This is the wake counterpart of {@link #parkKeys}: the two produce the
     * same kinds of keys, so a base is woken exactly when a changed formula could match it.
     * <p>
     * Keys are only computed when a base is currently parked under the same head and kind
     * ({@link #parkedCountsByHead}). This cannot suppress a needed wake. A key without such a
     * base has no base to wake now, and a base parked later does not need it either: within a
     * round the prover first picks candidates from the queue, which is when bases are parked,
     * and then applies the chosen rule, which is when formula changes are recorded. So every
     * change is recorded after all parks of its round, with the counts already raised, and a
     * change recorded before a base was parked concerns a formula the base's own failed match
     * already saw in the sequent. Skipping by head is also what makes recording cheap. The head
     * costs only the walk down the update chain. The two hashes, which walk the whole formula,
     * are computed only when a base is actually waiting for a formula with this head; without
     * this test, a proof step that changes a large formula, such as one carrying a whole
     * program, would hash it even though no base waits for such a formula.
     */
    void recordWakeKeysOf(Term formula, boolean inAntecedent) {
        if (parked == null || parked.isEmpty()) {
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
                    core.hashCodeModRenaming()));
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
                        firstArg.hashCodeModRenaming()));
                }
            }
        }
    }

    /**
     * A deep copy for a goal that splits into two: fresh map, fresh buckets, fresh pending set,
     * so the two goals park and wake independently (see the copy method of
     * {@link QueueRuleApplicationManager} for why sharing would change proofs). The stored
     * containers and the key components are never modified in place and stay shared. The copy
     * starts with the same parked population, so it inherits the sweep counters.
     */
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

    /** Consistency of {@link #parkedCountsByHead} with the parked map, for asserts. */
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

    /** Access to the parked map for the deep-copy test in this package. */
    @Nullable
    LinkedHashMap<WakeKey, Collection<RuleAppContainer>> parkedMapForTests() {
        return parked;
    }

    /** Insert an entry under the given key, bypassing {@link #parkKeys}; only for tests. */
    void parkForTests(WakeKey key, RuleAppContainer entry) {
        if (parked == null) {
            parked = new LinkedHashMap<>();
        }
        parked.computeIfAbsent(key, k -> new ArrayList<>(4)).add(entry);
        parkedCountsByHead.computeIfAbsent(key.head(), h -> new int[KINDS])[key.kind().ordinal()]++;
    }
}
