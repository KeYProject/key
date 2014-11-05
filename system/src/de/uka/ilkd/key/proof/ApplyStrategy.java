// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/*

Uses code by Hans Muller and Kathy Walrath from
http://java.sun.com/products/jfc/tsc/articles/threads/threads2.html

 */

package de.uka.ilkd.key.proof;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.core.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.core.RuleAppListener;
import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.proof.proofevent.NodeReplacement;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Debug;

/**
 * Applies rules in an automated fashion.
 * The caller should ensure that the strategy runs in its one thread
 */
public class ApplyStrategy {
    /**
     * <p>
     * Implementation of this interface are used in {@link ApplyStrategy} to
     * determine if the strategy should stop or continue.
     * </p>
     * <p>
     * The first check is done before a rule is applied on a {@link Goal} via
     * {@link #isGoalAllowed(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, Goal)}.
     * If this method returns {@code false} the strategy stops and the reason
     * shown to the user is computed via {@link #getGoalNotAllowedMessage(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, Goal)}.
     * </p>
     * <p>
     * The second check is after a rule was applied via
     * {@link #shouldStop(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, SingleRuleApplicationInfo)}.
     * If this method returns {@code true} the strategy stops and the reason
     * shown to the user is computed via {@link #getStopMessage(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, SingleRuleApplicationInfo)}.
     * </p>
     * <p>
     * <b>Attention: </b> It is possible that an {@link IStopCondition} has to check
     * one {@link Goal} with the same node multiple times. It is required that the
     * called check method always returns the same result for the same {@link Node} of a {@link Goal}.
     * </p>
     * @author Martin Hentschel
     */
    public static interface IStopCondition {
        /**
         * Returns the maximal amount of work needed to complete the task,
         * used to display a progress bar. Pass {@code 0} to indicate unknown size.
         * @param maxApplications The defined maximal number of rules to apply. Can be different to {@link StrategySettings#getMaxSteps()} in side proofs.
         * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to {@link StrategySettings#getTimeout()} in side proofs.
         * @param proof The current {@link Proof}.
         * @param goalChooser The current {@link IGoalChooser}.
         * @return The maximal amount of work or {@code 0} if it is unknown.
         */
        public int getMaximalWork(int maxApplications,
                                  long timeout,
                                  Proof proof,
                                  IGoalChooser goalChooser);

        /**
         * Checks if it is allowed to apply the next rule on the selected {@link Goal}
         * chosen by the {@link IGoalChooser} before it is applied.
         * If it is not allowed the apply strategy will stop.
         * @param maxApplications The defined maximal number of rules to apply. Can be different to {@link StrategySettings#getMaxSteps()} in side proofs.
         * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to {@link StrategySettings#getTimeout()} in side proofs.
         * @param proof The current {@link Proof}.
         * @param goalChooser The current {@link IGoalChooser}.
         * @param startTime The timestamp when the apply strategy has started, computed via {@link System#currentTimeMillis()}
         * @param countApplied The number of already applied rules.
         * @param goal The current {@link Goal} on which the next rule will be applied.
         * @return {@code true} rule application is allowed, {@code false} rule application is not allowed so stop apply strategy
         */
        public boolean isGoalAllowed(int maxApplications,
                                     long timeout,
                                     Proof proof,
                                     IGoalChooser goalChooser,
                                     long startTime,
                                     int countApplied,
                                     Goal goal);

        /**
         * Returns the reason why the previous check via
         * {@link #isGoalAllowed(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, Goal)}
         * has stopped the apply strategy.
         * @param maxApplications The defined maximal number of rules to apply. Can be different to {@link StrategySettings#getMaxSteps()} in side proofs.
         * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to {@link StrategySettings#getTimeout()} in side proofs.
         * @param proof The current {@link Proof}.
         * @param goalChooser The current {@link IGoalChooser}.
         * @param startTime The timestamp when the apply strategy has started, computed via {@link System#currentTimeMillis()}
         * @param countApplied The number of already applied rules.
         * @param goal The current {@link Goal} on which the next rule will be applied.
         * @return
         */
        public String getGoalNotAllowedMessage(int maxApplications,
                                               long timeout,
                                               Proof proof,
                                               IGoalChooser goalChooser,
                                               long startTime,
                                               int countApplied,
                                               Goal goal);

        /**
         * Checks after each applied rule if more rules should be applied or if the strategy should stop.
         * @param maxApplications The defined maximal number of rules to apply. Can be different to {@link StrategySettings#getMaxSteps()} in side proofs.
         * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to {@link StrategySettings#getTimeout()} in side proofs.
         * @param proof The current {@link Proof}.
         * @param goalChooser The current {@link IGoalChooser}.
         * @param startTime The timestamp when the apply strategy has started, computed via {@link System#currentTimeMillis()}
         * @param countApplied The number of already applied rules.
         * @param singleRuleApplicationInfo An optional {@link SingleRuleApplicationInfo}.
         * @return {@code true} stop strategy, {@code false} continue strategy and apply next rule.
         */
        public boolean shouldStop(int maxApplications,
                                  long timeout,
                                  Proof proof,
                                  IGoalChooser goalChooser,
                                  long startTime,
                                  int countApplied,
                                  SingleRuleApplicationInfo singleRuleApplicationInfo);

        /**
         * Returns a human readable message which explains why the previous
         * {@link #shouldStop(ApplyStrategy, Proof, IGoalChooser, long, int, SingleRuleApplicationInfo)}
         * has stopped the strategy.
         * @param maxApplications The defined maximal number of rules to apply. Can be different to {@link StrategySettings#getMaxSteps()} in side proofs.
         * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to {@link StrategySettings#getTimeout()} in side proofs.
         * @param proof The current {@link Proof}.
         * @param goalChooser The current {@link IGoalChooser}.
         * @param startTime The timestamp when the apply strategy has started, computed via {@link System#currentTimeMillis()}
         * @param countApplied The number of already applied rules.
         * @param singleRuleApplicationInfo An optional {@link SingleRuleApplicationInfo}.
         * @return The human readable message which explains the stop reason.
         */
        public String getStopMessage(int maxApplications,
                                     long timeout,
                                     Proof proof,
                                     IGoalChooser goalChooser,
                                     long startTime,
                                     int countApplied,
                                     SingleRuleApplicationInfo singleRuleApplicationInfo);
    }

    /**
     * <p>
     * Implementation of {@link IStopCondition} which stops the strategy
     * after a reached limit of rules or after a timeout in ms.
     * </p>
     * <p>
     * This is the default {@link IStopCondition} used during verification.
     * </p>
     * @author Martin Hentschel
     */
    public static final class AppliedRuleStopCondition implements IStopCondition {
        /**
         * {@inheritDoc}
         */
        @Override
        public int getMaximalWork(int maxApplications,
                                  long timeout,
                                  Proof proof,
                                  IGoalChooser goalChooser) {
            return maxApplications;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isGoalAllowed(int maxApplications,
                                     long timeout,
                                     Proof proof,
                                     IGoalChooser goalChooser,
                                     long startTime,
                                     int countApplied,
                                     Goal goal) {
            return true; // Default behavior is to accept all rules.
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String getGoalNotAllowedMessage(int maxApplications,
                                               long timeout,
                                               Proof proof,
                                               IGoalChooser goalChooser,
                                               long startTime,
                                               int countApplied,
                                               Goal goal) {
            return null;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean shouldStop(int maxApplications,
                                  long timeout,
                                  Proof proof,
                                  IGoalChooser goalChooser,
                                  long startTime,
                                  int countApplied,
                                  SingleRuleApplicationInfo singleRuleApplicationInfo) {
            return countApplied >= maxApplications ||
                   timeout >= 0 && System.currentTimeMillis() - startTime >= timeout;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String getStopMessage(int maxApplications,
                                     long timeout,
                                     Proof proof,
                                     IGoalChooser goalChooser,
                                     long startTime,
                                     int countApplied,
                                     SingleRuleApplicationInfo singleRuleApplicationInfo) {
            return "Maximal number of rule applications reached or timed out.";
        }
    }

    /**
     * Instances of this class are used to store if a rule could be applied automatically and if not
     * to store the reason why no rule applications could be performed. Because of performance reason the
     * success case returns the singleton {@link SingleRuleApplicationInfo#SUCCESS}
     */
    public static class SingleRuleApplicationInfo {

        private boolean success;
        private final String message;
        private final Goal goal;
        private RuleApp appliedRuleApp;

        SingleRuleApplicationInfo(Goal mayCloseableGoal, RuleApp appliedRuleApp) {
            this.message = "Rule applied successful";
            this.goal = mayCloseableGoal;
            this.appliedRuleApp = appliedRuleApp;
            this.success = true;
        }

        SingleRuleApplicationInfo(String message, Goal nonCloseableGoal, RuleApp appliedRuleApp) {
            this.message = message;
            this.goal = nonCloseableGoal;
            this.appliedRuleApp = appliedRuleApp;
            this.success = false;
        }

        public boolean isSuccess() {
            return success;
        }

        public Goal getGoal() {
            return goal;
        }

        public String message() {
            return message;
        }

        public RuleApp getAppliedRuleApp() {
            return appliedRuleApp;
        }
    }

    /** The final result of the strategy application is stored in this container
     * and returned to the instance that started the strategies.
     *
     * It contains statistic information about the number of applied rules, time needed or
     * number of closed goals. In case the rule application stopped at a non closeable goal,
     * this goal is also stored to allow the caller to e.g. present it to the user for interaction.
     *
     * In case of an unexpected, the thrown exception can be also retrieved from this container.
     */
    public static class ApplyStrategyInfo {
        private final String message;
        private final Goal nonCloseableGoal;

        private final Throwable error;

        private final long time;
        private final int appliedRuleAppsCount;
        private final int nrClosedGoals;
        private final Proof proof;

        public ApplyStrategyInfo(String message, Proof proof, Throwable error, Goal nonCloseableGoal,
                long time, int appliedRuleAppsCount, int nrClosedGoals) {
            this.message = message;
            this.proof = proof;
            this.error   = error;
            this.nonCloseableGoal = nonCloseableGoal;
            this.time    = time;
            this.appliedRuleAppsCount = appliedRuleAppsCount;
            this.nrClosedGoals = nrClosedGoals;
        }

        public String reason() {
            return message;
        }

        public Goal nonCloseableGoal() {
            return nonCloseableGoal;
        }

        public boolean isError() {
            return error != null;
        }

        public Throwable getException() {
            return error;
        }

        public long getTime() {
            return time;
        }

        public int getClosedGoals() {
            return nrClosedGoals;
        }

        public int getAppliedRuleApps() {
            return appliedRuleAppsCount;
        }

        public Proof getProof() {
            return proof;
        }

        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append("Apply Strategy Info:");
            sb.append("\n Message: ").append(message);
            sb.append("\n Error:").append(isError());
            if (isError()) {
                sb.append("\n ").append(error.getMessage());
            }
            sb.append("\n Applied Rules: ").append(appliedRuleAppsCount);
            sb.append("\n Time: ").append(time);
            sb.append("\n Closed Goals: ").append(nrClosedGoals);
            return sb.toString();
        }

    }

    public static final String PROCESSING_STRATEGY = "Processing Strategy";

    /** the proof that is worked with */
    private Proof proof;
    /** the maximum of allowed rule applications */
    private int maxApplications;

    /** The default {@link IGoalChooser} to choose goals to which rules are applied if the {@link StrategySettings} of the proof provides no customized one.*/
    private IGoalChooser defaultGoalChooser;

    /** number of rules automatically applied */
    private int countApplied = 0;
    private long time;

    /** interrupted by the user? */
    private boolean autoModeActive = false;

    /** We use an immutable list to store listeners to allow for
     * addition/removal within listener code */
    private ImmutableList<ProverTaskListener> proverTaskObservers = ImmutableSLList.nil();

    /** time in ms after which rule application shall be aborted, -1 disables timeout */
    private long timeout = -1;

    private boolean stopAtFirstNonCloseableGoal;

    protected int closedGoals;

    private boolean cancelled;

    IStopCondition stopCondition;

    IGoalChooser goalChooser;


    // Please create this object beforehand and re-use it.
    // Otherwise the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(IGoalChooser defaultGoalChooser) {
        this.defaultGoalChooser = defaultGoalChooser;
    }

    /** applies rules that are chosen by the active strategy
     * @return true iff a rule has been applied, false otherwise
     */
    private synchronized SingleRuleApplicationInfo
                            applyAutomaticRule (final IGoalChooser goalChooser,
                                                final IStopCondition stopCondition,
                                                boolean stopAtFirstNonClosableGoal) {
        // Look for the strategy ...
        RuleApp               app = null;
        Goal                  g;
        while ( ( g = goalChooser.getNextGoal () ) != null ) {
            if (!stopCondition.isGoalAllowed(maxApplications, timeout, proof,
                                             goalChooser, time, countApplied, g)) {
               return new SingleRuleApplicationInfo(
                       stopCondition.getGoalNotAllowedMessage(maxApplications, timeout, proof,
                                                              goalChooser, time, countApplied, g),
                       g, null);
            }
            app = g.getRuleAppManager().next();
            //Hack: built in rules may become applicable without BuiltInRuleAppIndex noticing---->
            if(app == null) {
                g.ruleAppIndex().scanBuiltInRules(g);
                app = g.getRuleAppManager().next();
            }
            //<-------

            if (app == null) {
                if (stopAtFirstNonClosableGoal) {
                    return new SingleRuleApplicationInfo("Could not close goal.", g, app);
                }
                goalChooser.removeGoal(g);
            } else {
                break;
            }
        }
         if (app == null) {
            return new SingleRuleApplicationInfo("No more rules automatically applicable to any goal.",
                                                 g, app);
        } else {
            assert g != null;
            g.apply(app);
            return new SingleRuleApplicationInfo(g, app);
        }
    }


    /**
     * applies rules until this is no longer
     * possible or the thread is interrupted.
     */
    private synchronized ApplyStrategyInfo doWork(final IGoalChooser goalChooser,
                                                  final IStopCondition stopCondition) {
        time = System.currentTimeMillis();
        SingleRuleApplicationInfo srInfo = null;
        try{
            Debug.out("Strategy started.");
            boolean shouldStop = stopCondition.shouldStop(maxApplications, timeout, proof,
                                                          goalChooser, time, countApplied, srInfo);

            while (!shouldStop) {
                srInfo = applyAutomaticRule(goalChooser, stopCondition, stopAtFirstNonCloseableGoal);
                if (!srInfo.isSuccess()) {
                    return new ApplyStrategyInfo(srInfo.message(), proof, null, srInfo.getGoal(),
                                                 System.currentTimeMillis()-time, countApplied,
                                                 closedGoals);
                }
                countApplied++;
                fireTaskProgress ();
                if (Thread.interrupted()) {
                    throw new InterruptedException();
                }
                shouldStop = stopCondition.shouldStop(maxApplications, timeout, proof, goalChooser,
                                                      time, countApplied, srInfo);
            }
            if (shouldStop) {
                return new ApplyStrategyInfo(
                        stopCondition.getStopMessage(maxApplications, timeout, proof, goalChooser,
                                                     time, countApplied, srInfo),
                        proof, null, (Goal) null, System.currentTimeMillis()-time,
                        countApplied, closedGoals);
            }
        } catch (InterruptedException e) {
            cancelled = true;
            return new ApplyStrategyInfo("Interrupted.", proof, null, goalChooser.getNextGoal(),
                                         System.currentTimeMillis()-time, countApplied, closedGoals);
        } catch (Throwable t) { // treated later in finished()
            t.printStackTrace();
            return new ApplyStrategyInfo("Error.", proof, t, null, System.currentTimeMillis()-time,
                                         countApplied, closedGoals);
        } finally{
            time = System.currentTimeMillis()-time;
            Debug.out("Strategy stopped.");
            Debug.out("Applied ", countApplied);
            Debug.out("Time elapsed: ", time);
        }
        assert srInfo != null;
        return new ApplyStrategyInfo(srInfo.message(), proof, null, srInfo.getGoal(), time,
                                     countApplied, closedGoals);
    }

    private synchronized void fireTaskStarted (int maxSteps) {
        for (ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskStarted(PROCESSING_STRATEGY, maxSteps);
        }
    }

    private synchronized void fireTaskProgress () {
        for (ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskProgress(countApplied);
        }
    }

    private synchronized void fireTaskFinished (TaskFinishedInfo info) {
        for (ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskFinished(info);
        }
    }


    private void init(Proof newProof, ImmutableList<Goal> goals, int maxSteps, long timeout) {
        this.proof      = newProof;
        maxApplications = maxSteps;
        this.timeout    = timeout;
        countApplied    = 0;
        closedGoals     = 0;
        cancelled       = false;
        stopCondition = proof.getSettings().getStrategySettings().getApplyStrategyStopCondition();
        assert stopCondition != null;
        goalChooser = getGoalChooserForProof(proof);
        assert goalChooser != null;
        goalChooser.init ( newProof, goals );
        setAutoModeActive(true);
        fireTaskStarted (stopCondition.getMaximalWork(maxSteps, timeout, newProof, goalChooser));
    }

    public synchronized ApplyStrategyInfo start(Proof proof, Goal goal) {
        return start(proof, ImmutableSLList.<Goal>nil().prepend(goal));
    }

    public synchronized ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals) {

        ProofSettings settings = proof.getSettings();
        StrategySettings stratSet = settings.getStrategySettings();
        int maxSteps = stratSet.getMaxSteps();
        long timeout = stratSet.getTimeout();

        boolean stopAtFirstNonCloseableGoal =
                proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(
                        StrategyProperties.STOPMODE_OPTIONS_KEY)
                        .equals(StrategyProperties.STOPMODE_NONCLOSE);
        return start(proof, goals, maxSteps, timeout, stopAtFirstNonCloseableGoal);
    }

    /**
     * This entry point to the proof may provide inconsistent data. The
     * properties within the proof may differ to the explicit data. This is
     * discouraged.
     *
     * @return
     *
     * @deprecated Use {@link #start(Proof, ImmutableList)}. Adjust the settings
     *             beforehand if needed
     */
    @Deprecated
    public synchronized ApplyStrategyInfo start(Proof proof,
                                                ImmutableList<Goal> goals,
                                                int maxSteps,
                                                long timeout,
                                                boolean stopAtFirstNonCloseableGoal) {
        assert proof != null;

        this.stopAtFirstNonCloseableGoal = stopAtFirstNonCloseableGoal;

        ProofTreeListener treeListener =
                prepareStrategy(proof, goals, maxSteps, timeout);
        ApplyStrategyInfo result = executeStrategy(treeListener);
        finishStrategy(result);
        return result;
    }


    private ProofTreeListener prepareStrategy(Proof proof, ImmutableList<Goal> goals,
                                              int maxSteps, long timeout) {
        ProofTreeListener treeListener = new ProofTreeAdapter() {
            @Override
            public void proofGoalsAdded(ProofTreeEvent e) {
                ImmutableList<Goal> newGoals = e.getGoals();
                // Check for a closed goal ...
                if (newGoals.size() == 0){
                    // No new goals have been generated ...
                    closedGoals++;
                }
            }
        };
        proof.addProofTreeListener(treeListener);
        init(proof, goals, maxSteps, timeout);

        return treeListener;
    }

    private ApplyStrategyInfo executeStrategy(ProofTreeListener treeListener) {
        assert proof != null;

        ProofListener pl = new ProofListener();
        proof.addRuleAppListener( pl );
        ApplyStrategyInfo result = null;
        try {
            result = doWork(goalChooser, stopCondition);
        } finally {
            proof.removeProofTreeListener(treeListener);
            proof.removeRuleAppListener(pl);
            setAutoModeActive(false);
        }
        return result;
    }

    private void finishStrategy(ApplyStrategyInfo result) {
        assert result != null; // CS
        proof.addAutoModeTime(result.getTime());
        fireTaskFinished (new DefaultTaskFinishedInfo(this, result, proof, result.getTime(),
                                                      result.getAppliedRuleApps(),
                                                      result.getClosedGoals()));
    }

    // Used to combine multiple iteratively called proofs and integrate their results in final result
    private ApplyStrategyInfo joinStrategyInfos(ApplyStrategyInfo result,
                                                ApplyStrategyInfo subResult) {
        if(result == null)
            return subResult;
        String msg = subResult.reason();
        Proof prf = subResult.getProof();
        Throwable err = subResult.getException();
        if(result.isError())
            err = result.getException();
        Goal go = subResult.nonCloseableGoal();
        long tme = result.getTime() + subResult.getTime();
        int appl = result.getAppliedRuleApps() + subResult.getAppliedRuleApps();
        int clsd = result.getClosedGoals() + subResult.getClosedGoals();
        result = new ApplyStrategyInfo(msg,prf,err,go,tme,appl,clsd);
        return result;
    }

    /**
     * Returns the {@link IGoalChooser} to use for the given {@link Proof}.
     * This is the custom one defined in the proof's {@link StrategySettings}
     * or the default one of this {@link ApplyStrategy#defaultGoalChooser} otherwise.
     * @param proof The {@link Proof} for which an {@link IGoalChooser} is required.
     * @return The {@link IGoalChooser} to use.
     */
    private IGoalChooser getGoalChooserForProof(Proof proof) {
       IGoalChooser chooser = null;
       if (proof != null) {
          chooser = proof.getSettings().getStrategySettings().getCustomApplyStrategyGoalChooser();
       }
       return chooser != null ? chooser : defaultGoalChooser;
    }
    public synchronized void addProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers = proverTaskObservers.prepend(observer);
    }

    public synchronized void removeProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers = proverTaskObservers.removeAll(observer);
    }


    private class ProofListener implements RuleAppListener {

        /** invoked when a rule has been applied */
        public void ruleApplied(ProofEvent e) {
            if (!isAutoModeActive()) return;
            RuleAppInfo rai = e.getRuleAppInfo ();
            if ( rai == null )
                return;

            synchronized ( ApplyStrategy.this ) {
                ImmutableList<Goal>                newGoals = ImmutableSLList.<Goal>nil();
                Iterator<NodeReplacement> it       = rai.getReplacementNodes ();
                Node                      node;
                Goal                      goal;

                while ( it.hasNext () ) {
                    node = it.next ().getNode ();
                    goal = proof.getGoal ( node );
                    if ( goal != null )
                        newGoals = newGoals.prepend ( goal );
                }

                final IGoalChooser goalChooser = getGoalChooserForProof(proof);
                goalChooser.updateGoalList ( rai.getOriginalNode (), newGoals );
            }
        }
    }

    private boolean isAutoModeActive() {
        return autoModeActive;
    }

    private void setAutoModeActive(boolean autoModeActive) {
        this.autoModeActive = autoModeActive;
    }

    /**Used by, e.g., {@code InteractiveProver.clear()} in order to prevent memory leaking.
     * When a proof obligation is abandoned all references to the proof must be reset.
     * @author gladisch */
    public void clear(){
        final IGoalChooser goalChooser = getGoalChooserForProof(proof);
        proof = null;
        if(goalChooser!=null){
            goalChooser.init(null, ImmutableSLList.<Goal>nil());
        }
    }

    /**
     * Returns true iff the last run has been stopped due to a received
     * {@link InterruptedException}. This exception would have been swallowed by
     * the system. However, the cancelled flag is set in this case which allows
     * detection of such a condition.
     *
     * @return whether the last run has been interrupted
     */
    public boolean hasBeenInterrupted() {
        return cancelled;
    }
}
