package de.uka.ilkd.key.java;

import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.PrefixTermTacletAppIndexCacheImpl.CacheKey;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermTacletAppIndex;
import de.uka.ilkd.key.proof.TermTacletAppIndexCacheSet;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.AbstractBetaFeature.TermInfo;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesGraph;
import de.uka.ilkd.key.strategy.quantifierHeuristics.TriggersSet;
import de.uka.ilkd.key.util.LRUCache;

/**
 * <p>
 * Instances of this class provides all caches used by an individual {@link Proof}
 * or more precise by its {@link Services}.
 * </p>
 * <p>
 * This is a redesign of the old static caches which were implemented via final static
 * {@link Map}s like 
 * {@code private static final Map<CacheKey, TermTacletAppIndex> termTacletAppIndexCache = new LRUCache<CacheKey, TermTacletAppIndex> ( MAX_TERM_TACLET_APP_INDEX_ENTRIES );}.
 * </p>  
 * <p>
 * The old idea that memory is reused and shared between multiple {@link Proof}s
 * by static variables is wrong, because in practice it wastes memory. 
 * The problem is that cached data structures
 * can become large, especially in case of {@link #getTermTacletAppIndexCache()}.
 * The static cache is filled with these large data structures and 
 * not freed even if all {@link Proof}s are disposed ({@link Proof#isDisposed()}).
 * This can fill quickly (about 30 done {@link Proof}s) the whole memory.
 * A new {@link Proof} which does not profit from the cached data structure
 * has then no free memory to live in which makes the whole <b>system unusable slow</b>.
 * </p>
 * <p>
 * The goal of this new design is to avoid all static cache variables and
 * to collect them instead as instance variables in this class. 
 * Each {@link Proof} has its own {@link Services}
 * which provides a {@link ServiceCaches} instance to use via
 * {@link Services#getCaches()}. The advantages are:
 * <ul>
 *    <li>The cache contains only usable content and nothing from other {@link Proof}s not relevant for the current {@link Proof}.</li>
 *    <li>The whole memory is freed when a {@link Proof} is disposed via {@link Proof#dispose()}.</li>
 *    <li>Multiple {@link Proof}s at the same time are faster because they can fill the cache up to the fixed limit. Also the user interface profits from it when a user switches between proofs.</li>
 *    <li>Even if multiple large {@link Proof}s exist at the same time it seems to be no problem that multiple caches exist.</li>
 *    <li>The old behavior in which multiple {@link Proof}s use the same cache can be realized just by using the same {@link ServiceCaches} instance. This can be useful for instance in side proofs.</li>
 * </ul>
 * </p>
 * @author Martin Hentschel
 */
public class ServiceCaches {
   /**
    * The maximal number of index entries in {@link #getTermTacletAppIndexCache()}.
    */
   public static final int MAX_TERM_TACLET_APP_INDEX_ENTRIES = 5000;
   
   /**
    * The cache used by {@link TermTacletAppIndexCacheSet} instances.
    */
   private final Map<CacheKey, TermTacletAppIndex> termTacletAppIndexCache = new LRUCache<CacheKey, TermTacletAppIndex> ( MAX_TERM_TACLET_APP_INDEX_ENTRIES );

   /*
    * Table of formulas which could be splitted using the beta rule
    * This is the cache the method "isBetaCandidate" uses
    *
    *    keys: Term              values: TermInfo
    */
   private final LRUCache<Term, TermInfo> betaCandidates = new LRUCache<Term, TermInfo> (1000);

   private final LRUCache<PosInOccurrence, RuleAppCost> ifThenElseMalusCache = new LRUCache<PosInOccurrence, RuleAppCost>(1000); 

   private final LRUCache<Operator, Integer> introductionTimeCache = new LRUCache<Operator, Integer> ( 10000 );
   
   private final LRUCache<Term, Monomial> monomialCache =  new LRUCache<Term, Monomial> ( 2000 );

   private final LRUCache<Term, Polynomial> polynomialCache = new LRUCache<Term, Polynomial> ( 2000 );

   /**a <code>HashMap</code> from <code>Term</code> to 
    * <code>TriggersSet</code> uses to cache all created TriggersSets*/
   private final Map<Term, TriggersSet> triggerSetCache = new LRUCache<Term, TriggersSet>(1000);

   /**
    * Map from  <code>Term</code>(allTerm) to <code>ClausesGraph</code> 
    */
   private final Map<Term, ClausesGraph> graphCache = new LRUCache<Term, ClausesGraph> (1000);

   /**
    * Cache used by the TermFactory to avoid unnecessary creation of terms
    */
   private final Map<Term, Term> termCache = new LRUCache<Term, Term>(20000);

   /**
    * Cache used by TypeComparisonCondition
    */
   private final Map<Sort,Map<Sort,Boolean>> disjointnessCache = new WeakHashMap<Sort,Map<Sort,Boolean>>();
   
   /**
    * Returns the cache used by {@link TermTacletAppIndexCacheSet} instances.
    * @return The cache used by {@link TermTacletAppIndexCacheSet} instances.
    */
   public Map<CacheKey, TermTacletAppIndex> getTermTacletAppIndexCache() {
      return termTacletAppIndexCache;
   }

   public LRUCache<Term, TermInfo> getBetaCandidates() {
      return betaCandidates;
   }

   public LRUCache<PosInOccurrence, RuleAppCost> getIfThenElseMalusCache() {
      return ifThenElseMalusCache;
   }

   public LRUCache<Operator, Integer> getIntroductionTimeCache() {
      return introductionTimeCache;
   }
   
   public LRUCache<Term, Monomial> getMonomialCache() {
      return monomialCache;
   }

   public LRUCache<Term, Polynomial> getPolynomialCache() {
      return polynomialCache;
   }

   public Map<Term, TriggersSet> getTriggerSetCache() {
      return triggerSetCache;
   }

   public Map<Term, ClausesGraph> getGraphCache() {
      return graphCache;
   }

   public Map<Term, Term> getTermFactoryCache() {
       return termCache;
   }

   public Map<Sort, Map<Sort, Boolean>> getDisjointnessCache() {
       return disjointnessCache;
   }
}
