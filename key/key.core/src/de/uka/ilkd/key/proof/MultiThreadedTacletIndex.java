package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.Future;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;

/**
 * A multi-threaded taclet index implementation. It executes method 
 * {@link #matchTaclets(ImmutableList, RuleFilter, PosInOccurrence, Services)}
 * using multiple threads (depending on the number of taclets being matched 
 * and number of available processors).
 *
 * Do not create this index directly. Use the {@link TacletIndexKit#createTacletIndex()} resp.
 * {@link TacletIndexKit#createTacletIndex(Iterable)}.
 * @see TacletIndex
 * @see TacletIndexKit 
 */
final class MultiThreadedTacletIndex extends TacletIndex {

    private static ForkJoinPool execs = new ForkJoinPool();// ForkJoinPool.commonPool(); <- Use this once we switch to Java 8

    MultiThreadedTacletIndex(Iterable<Taclet> tacletSet) {
        super(tacletSet);
    }

    MultiThreadedTacletIndex() {
        super();
    }

    private MultiThreadedTacletIndex(
            HashMap<Object, ImmutableList<NoPosTacletApp>> rwList,
            HashMap<Object, ImmutableList<NoPosTacletApp>> antecList,
            HashMap<Object, ImmutableList<NoPosTacletApp>> succList,
            ImmutableList<NoPosTacletApp> noFindList,
            HashSet<NoPosTacletApp> partialInstantiatedRuleApps) {
        super(rwList, antecList, succList, noFindList, partialInstantiatedRuleApps);
    }

    /** 
     * {@inheritDoc}
     */
    @SuppressWarnings("unchecked")
    @Override
    public TacletIndex copy() {
        return new MultiThreadedTacletIndex((HashMap<Object, ImmutableList<NoPosTacletApp>>)rwList.clone(), 
                (HashMap<Object, ImmutableList<NoPosTacletApp>>)antecList.clone(), 
                (HashMap<Object, ImmutableList<NoPosTacletApp>>)succList.clone(), 
                noFindList, (HashSet<NoPosTacletApp>)partialInstantiatedRuleApps.clone());
    }

    /** 
     * {@inheritDoc}
     */
    @Override
    protected ImmutableList<NoPosTacletApp> matchTaclets(
            ImmutableList<NoPosTacletApp> tacletApps, RuleFilter p_filter,
            PosInOccurrence pos, Services services) { 

        ImmutableList<NoPosTacletApp> result = ImmutableSLList.<NoPosTacletApp>nil();
        if (tacletApps == null) {
            return result;
        }

        if (tacletApps.size() > 256) {
            NoPosTacletApp[] toMatch = tacletApps.toArray(NoPosTacletApp.class);                        
            final int localParallelism = (toMatch.length >> 5 > execs.getParallelism() ?  execs.getParallelism() : toMatch.length >> 5);
            final int partitionSize = toMatch.length/localParallelism;

            List<TacletSetMatchTask> forks = new ArrayList<>();

            for (int lower = 0; lower<toMatch.length; lower+=partitionSize) {
                int upper = lower + partitionSize;
                upper = upper <= toMatch.length ? upper : toMatch.length;
                forks.add(new TacletSetMatchTask(toMatch, lower, upper, pos, p_filter, services));
            }
            
            List<NoPosTacletApp> matchedRules = new LinkedList<NoPosTacletApp>();
            
            try {
                for (Future<List<NoPosTacletApp>> res : execs.invokeAll(forks)) {
                    matchedRules.addAll(res.get());
                }
            }
            catch (InterruptedException | ExecutionException e) {
                throw (IllegalStateException) new IllegalStateException().initCause(e);
            }
            result = result.prepend(matchedRules);
        } else {
            for (final NoPosTacletApp tacletApp : tacletApps) {
                if ( !p_filter.filter(tacletApp.taclet()) ) {
                    continue;
                }                    
                final NoPosTacletApp newTacletApp =
                        tacletApp.matchFind(pos, services);
                if (newTacletApp != null) {
                    result = result.prepend(newTacletApp);
                }
            } 
        }

        return result;  
    }

    /**
     * The callable implementing the actual matching task. 
     */
    static class TacletSetMatchTask implements Callable<List<NoPosTacletApp>> {
        private NoPosTacletApp[] toMatch;
        private final int lower;
        private final int upper;
        private Services services;
        private PosInOccurrence pos;
        private RuleFilter ruleFilter;

        /**
         * Creates a task which matches all taclets in {@code toMatch}
         * from {@code lower} including to {@code upper} excluding
         * against the term at position {@code pos}. Only taclets
         * passing the filter {@code ruleFilter} are considered
         * @param toMatch the list containing the taclets to be matched
         * @param lower the index (incl.) where to start         
         * @param upper the index (excl.) where to stop
         * @param pos the {@link PosInOccurrence} refering to the term to match
         * @param ruleFilter {@link RuleFilter} constraining the taclets to be matched
         * @param services the {@link Services}
         */
        public TacletSetMatchTask(NoPosTacletApp[] toMatch, int lower,
                int upper, PosInOccurrence pos, RuleFilter ruleFilter,
                Services services) {
            this.toMatch = toMatch;
            this.lower = lower;
            this.upper = upper;
            this.services = services;
            this.pos = pos;
            this.ruleFilter = ruleFilter;
        }

        @Override
        public List<NoPosTacletApp> call() {
            List<NoPosTacletApp> result = new LinkedList<>();
            for(int i = lower; i < upper; i++) {
                NoPosTacletApp tacletApp = toMatch[i];
                if ( !ruleFilter.filter(tacletApp.taclet()) ) {
                    continue;
                }                    
                final NoPosTacletApp newTacletApp =
                        tacletApp.matchFind(pos, services);
                if (newTacletApp != null) {
                    result.add(newTacletApp);
                }
            } 
            return result;
        }

    }
}
