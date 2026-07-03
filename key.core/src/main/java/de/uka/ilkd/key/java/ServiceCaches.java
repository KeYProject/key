/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import java.util.concurrent.ConcurrentHashMap;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.PrefixTermTacletAppIndexCacheImpl.CacheKey;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermTacletAppIndex;
import de.uka.ilkd.key.proof.TermTacletAppIndexCacheSet;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
import de.uka.ilkd.key.strategy.IfInstantiationCachePool;
import de.uka.ilkd.key.strategy.feature.AbstractBetaFeature.TermInfo;
import de.uka.ilkd.key.strategy.feature.AppliedRuleAppsNameCache;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesGraph;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;
import de.uka.ilkd.key.strategy.quantifierHeuristics.TriggersSet;

import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.proof.SessionCaches;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.rules.instantiation.caches.AssumesFormulaInstantiationCache;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.util.ConcurrentLruCache;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

/**
 * <p>
 * Instances of this class provides all caches used by an individual {@link Proof} or more precise
 * by its {@link Services}.
 * </p>
 * <p>
 * This is a redesign of the old static caches which were implemented via final static {@link Map}s
 * like
 * {@code private static final Map<CacheKey, TermTacletAppIndex> termTacletAppIndexCache = new LRUCache<CacheKey, TermTacletAppIndex> ( MAX_TERM_TACLET_APP_INDEX_ENTRIES );}.
 * </p>
 * <p>
 * The old idea that memory is reused and shared between multiple {@link Proof}s by static variables
 * is wrong, because in practice it wastes memory. The problem is that cached data structures can
 * become large, especially in case of {@link #getTermTacletAppIndexCache()}. The static cache is
 * filled with these large data structures and not freed even if all {@link Proof}s are disposed
 * ({@link Proof#isDisposed()}). This can fill quickly (about 30 done {@link Proof}s) the whole
 * memory. A new {@link Proof} which does not profit from the cached data structure has then no free
 * memory to live in which makes the whole <b>system unusable slow</b>.
 * </p>
 * <p>
 * The goal of this new design is to avoid all static cache variables and to collect them instead as
 * instance variables in this class. Each {@link Proof} has its own {@link Services} which provides
 * a {@link ServiceCaches} instance to use via {@link Services#getCaches()}. The advantages are:
 * <ul>
 * <li>The cache contains only usable content and nothing from other {@link Proof}s not relevant for
 * the current {@link Proof}.</li>
 * <li>The whole memory is freed when a {@link Proof} is disposed via {@link Proof#dispose()}.</li>
 * <li>Multiple {@link Proof}s at the same time are faster because they can fill the cache up to the
 * fixed limit. Also the user interface profits from it when a user switches between proofs.</li>
 * <li>Even if multiple large {@link Proof}s exist at the same time it seems to be no problem that
 * multiple caches exist.</li>
 * <li>The old behavior in which multiple {@link Proof}s use the same cache can be realized just by
 * using the same {@link ServiceCaches} instance. This can be useful for instance in side
 * proofs.</li>
 * </ul>
 * </p>
 *
 * @author Martin Hentschel
 */
public class ServiceCaches implements SessionCaches {
    /**
     * The maximal number of index entries in {@link #getTermTacletAppIndexCache()}.
     */
    public static final int MAX_TERM_TACLET_APP_INDEX_ENTRIES = 5000;

    /**
     * The cache used by {@link TermTacletAppIndexCacheSet} instances.
     */
    private final Map<CacheKey, TermTacletAppIndex> termTacletAppIndexCache =
        new ConcurrentLruCache<>(MAX_TERM_TACLET_APP_INDEX_ENTRIES);

    /*
     * Table of formulas which could be splitted using the beta rule This is the cache the method
     * "isBetaCandidate" uses
     *
     * keys: Term values: TermInfo
     *
     * NOTE (multithreading effort, branch bubel/mt-goals): the LRU caches below use
     * ConcurrentLruCache (exact, single-lock) so they are safe under concurrent matching while
     * preserving EXACT LRU eviction -- behaviour-preserving. Exact eviction matters for any cache
     * whose value could be recomputed differently under a different access order after an eviction
     * (e.g. the term interning cache); approximate/striped eviction was shown to change proofs.
     * (introductionTimeCache is NOT such a case: its entry is an operator's introducer depth from
     * the root, identical for every goal below that introducer, so it is goal-/order-independent --
     * bypassing it leaves proofs unchanged.) The Weak caches stay wrapped in
     * Collections.synchronizedMap.
     */
    private final Map<JTerm, TermInfo> betaCandidates =
        new ConcurrentLruCache<>(1000);

    private final Map<PosInOccurrence, RuleAppCost> ifThenElseMalusCache =
        new ConcurrentLruCache<>(1000);

    /**
     * the introduction time cache used by {@code AbstractMonomialSmallerThanFeature} for Skolem
     * constants
     */
    private final Map<Operator, Integer> introductionTimeCache =
        new ConcurrentLruCache<>(10000);

    /**
     * Per-proof cache for {@code CostReuse}'s feature-locality classification (taclet -> its
     * reuse-eligibility verdict). Held here, like the other proof-scoped caches, so it is freed
     * with
     * the proof and never shared between proofs with different taclet options. Values are opaque to
     * this class (a {@code CostReuse.Eligibility}, or its ineligible sentinel) to keep this package
     * independent of the strategy package.
     */
    private final Map<Taclet, Object> costReuseClassificationCache = new ConcurrentHashMap<>();

    private final Map<org.key_project.logic.Term, Monomial> monomialCache =
        new ConcurrentLruCache<>(2000);

    private final Map<org.key_project.logic.Term, Polynomial> polynomialCache =
        new ConcurrentLruCache<>(2000);

    /**
     * a <code>HashMap</code> from <code>Term</code> to <code>TriggersSet</code> uses to cache all
     * created TriggersSets
     */
    private final Map<org.key_project.logic.Term, TriggersSet> triggerSetCache =
        new ConcurrentLruCache<>(1000);

    /**
     * Map from <code>Term</code>(allTerm) to <code>ClausesGraph</code>
     */
    private final Map<org.key_project.logic.Term, ClausesGraph> graphCache =
        new ConcurrentLruCache<>(1000);

    /**
     * Cache used by the TermFactory to avoid unnecessary creation of terms
     */
    private final Map<JTerm, JTerm> termCache = new ConcurrentLruCache<>(20000);

    /**
     * Cache used by TypeComparisonCondition
     */
    private final Map<Sort, Map<Sort, Boolean>> disjointnessCache =
        Collections.synchronizedMap(new WeakHashMap<>());

    /**
     * Cache used by HandleArith for caching formatted terms
     */
    private final Map<JTerm, JTerm> formattedTermCache =
        new ConcurrentLruCache<>(5000);

    /**
     * Caches used bu HandleArith to cache proof results
     */
    private final Map<JTerm, JTerm> provedByArithFstCache =
        new ConcurrentLruCache<>(5000);

    private final Map<Pair<JTerm, JTerm>, JTerm> provedByArithSndCache =
        new ConcurrentLruCache<>(5000);

    /** Cache used by the exhaustive macro */
    private final Map<Node, PosInOccurrence> exhaustiveMacroCache =
        Collections.synchronizedMap(new WeakHashMap<>());

    /** Cache used by the ifinstantiator */
    private final IfInstantiationCachePool ifInstantiationCache = new IfInstantiationCachePool();

    /** Cache used IfFormulaInstSeq */
    private final AssumesFormulaInstantiationCache assumesFormulaInstantiationCache =
        new AssumesFormulaInstantiationCache();

    /** applied rule apps name cache */
    private final AppliedRuleAppsNameCache appliedRuleAppsNameCache =
        new AppliedRuleAppsNameCache();

    /** Cache used by EqualityConstraint to speed up meta variable search */
    private final Map<org.key_project.logic.Term, ImmutableSet<Metavariable>> mvCache =
        new ConcurrentLruCache<>(2000);

    /**
     * Cache used by {@link de.uka.ilkd.key.rule.label.OriginTermLabelRefactoring}: the
     * origins of a term and all its subterms. Terms are immutable, so the set never
     * changes for a given term.
     */
    private final Map<JTerm, Set<Origin>> subtermOriginsCache =
        new ConcurrentLruCache<>(20000);


    /**
     * Returns the cache used by {@link TermTacletAppIndexCacheSet} instances.
     *
     * @return The cache used by {@link TermTacletAppIndexCacheSet} instances.
     */
    public final Map<CacheKey, TermTacletAppIndex> getTermTacletAppIndexCache() {
        return termTacletAppIndexCache;
    }

    /**
     * Returns the cache used by
     * {@link de.uka.ilkd.key.rule.label.OriginTermLabelRefactoring}.
     *
     * @return map from a term to the origins of the term and all its subterms
     */
    public final Map<JTerm, Set<Origin>> getSubtermOriginsCache() {
        return subtermOriginsCache;
    }

    public final Map<JTerm, TermInfo> getBetaCandidates() {
        return betaCandidates;
    }

    public final Map<PosInOccurrence, RuleAppCost> getIfThenElseMalusCache() {
        return ifThenElseMalusCache;
    }

    /**
     * returns the introduction time cache used by {@code AbstractMonomialSmallerThanFeature} for
     * Skolem constants
     */
    public final Map<Operator, Integer> getIntroductionTimeCache() {
        return introductionTimeCache;
    }

    public final Map<Taclet, Object> getCostReuseClassificationCache() {
        return costReuseClassificationCache;
    }

    public final Map<org.key_project.logic.Term, Monomial> getMonomialCache() {
        return monomialCache;
    }

    public final Map<org.key_project.logic.Term, Polynomial> getPolynomialCache() {
        return polynomialCache;
    }

    public final Map<org.key_project.logic.Term, TriggersSet> getTriggerSetCache() {
        return triggerSetCache;
    }

    public final Map<org.key_project.logic.Term, ClausesGraph> getGraphCache() {
        return graphCache;
    }

    public final Map<JTerm, JTerm> getTermFactoryCache() {
        return termCache;
    }

    public final Map<Sort, Map<Sort, Boolean>> getDisjointnessCache() {
        return disjointnessCache;
    }

    public final Map<JTerm, JTerm> getFormattedTermCache() {
        return formattedTermCache;
    }

    public final Map<JTerm, JTerm> getProvedByArithFstCache() {
        return provedByArithFstCache;
    }

    public final Map<Pair<JTerm, JTerm>, JTerm> getProvedByArithSndCache() {
        return provedByArithSndCache;
    }

    public final Map<Node, PosInOccurrence> getExhaustiveMacroCache() {
        return exhaustiveMacroCache;
    }

    public final IfInstantiationCachePool getIfInstantiationCache() {
        return ifInstantiationCache;
    }

    public final AssumesFormulaInstantiationCache getAssumesFormulaInstantiationCache() {
        return assumesFormulaInstantiationCache;
    }

    public AppliedRuleAppsNameCache getAppliedRuleAppsNameCache() {
        return appliedRuleAppsNameCache;
    }

    public Map<org.key_project.logic.Term, ImmutableSet<Metavariable>> getMVCache() {
        return mvCache;
    }

}
