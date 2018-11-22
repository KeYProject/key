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

package de.uka.ilkd.key.prover.impl;


import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.StopCondition;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Debug;

/**
 * Applies rules in an automated fashion.
 * The caller should ensure that the strategy runs in its one thread
 */
public class ApplyStrategy implements ProverCore {
    public static final String PROCESSING_STRATEGY = "Processing Strategy";

    /** the proof that is worked with */
    private Proof proof;
    /** the maximum of allowed rule applications */
    private int maxApplications;

    /** The default {@link GoalChooser} to choose goals to which rules are applied if the {@link StrategySettings} of the proof provides no customized one.*/
    private GoalChooser defaultGoalChooser;

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

    private StopCondition stopCondition;

    private GoalChooser goalChooser;


    // Please create this object beforehand and re-use it.
    // Otherwise the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(GoalChooser defaultGoalChooser) {
        this.defaultGoalChooser = defaultGoalChooser;
    }

    /** applies rules that are chosen by the active strategy
     * @return true iff a rule has been applied, false otherwise
     */
    private synchronized SingleRuleApplicationInfo
                            applyAutomaticRule (final GoalChooser goalChooser,
                                                final StopCondition stopCondition,
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
            if (g.apply(app).isEmpty()) {
            	closedGoals++;
            }
            return new SingleRuleApplicationInfo(g, app);
        }
    }


    /**
     * applies rules until this is no longer
     * possible or the thread is interrupted.
     */
    private synchronized ApplyStrategyInfo doWork(final GoalChooser goalChooser,
                                                  final StopCondition stopCondition) {
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
            time = (System.currentTimeMillis()-time);
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
            ptl.taskStarted(new DefaultTaskStartedInfo(TaskKind.Strategy, PROCESSING_STRATEGY, maxSteps));
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

    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof, de.uka.ilkd.key.proof.Goal)
	 */
    @Override
	public synchronized ApplyStrategyInfo start(Proof proof, Goal goal) {
        return start(proof, ImmutableSLList.<Goal>nil().prepend(goal));
    }

    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof, org.key_project.util.collection.ImmutableList)
	 */
    @Override
	public synchronized ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals) {
       ProofSettings settings = proof.getSettings();
       StrategySettings stratSet = settings.getStrategySettings();
       return start(proof, goals, stratSet);
    }

    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof, org.key_project.util.collection.ImmutableList, de.uka.ilkd.key.settings.StrategySettings)
	 */
    @Override
	public synchronized ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals, StrategySettings stratSet) {

        int maxSteps = stratSet.getMaxSteps();
        long timeout = stratSet.getTimeout();

        boolean stopAtFirstNonCloseableGoal =
                proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(
                        StrategyProperties.STOPMODE_OPTIONS_KEY)
                        .equals(StrategyProperties.STOPMODE_NONCLOSE);
        return start(proof, goals, maxSteps, timeout, stopAtFirstNonCloseableGoal);
    }

    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof, org.key_project.util.collection.ImmutableList, int, long, boolean)
	 */
    @Override
	public synchronized ApplyStrategyInfo start(Proof proof,
                                                ImmutableList<Goal> goals,
                                                int maxSteps,
                                                long timeout,
                                                boolean stopAtFirstNonCloseableGoal) {
        assert proof != null;

        this.stopAtFirstNonCloseableGoal = stopAtFirstNonCloseableGoal;

        init(proof, goals, maxSteps, timeout);
        ApplyStrategyInfo result = executeStrategy();
        finishStrategy(result);
        return result;
    }

    private ApplyStrategyInfo executeStrategy() {
        assert proof != null;

        ProofListener pl = new ProofListener();
        proof.addRuleAppListener( pl );
        ApplyStrategyInfo result = null;
        try {
            result = doWork(goalChooser, stopCondition);
        } finally {
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

    /**
     * Returns the {@link GoalChooser} to use for the given {@link Proof}.
     * This is the custom one defined in the proof's {@link StrategySettings}
     * or the default one of this {@link ApplyStrategy#defaultGoalChooser} otherwise.
     * @param proof The {@link Proof} for which an {@link GoalChooser} is required.
     * @return The {@link GoalChooser} to use.
     */
    private GoalChooser getGoalChooserForProof(Proof proof) {
       GoalChooser chooser = null;
       if (proof != null) {
          chooser = proof.getSettings().getStrategySettings().getCustomApplyStrategyGoalChooser();
       }
       return chooser != null ? chooser : defaultGoalChooser;
    }
    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#addProverTaskObserver(de.uka.ilkd.key.prover.ProverTaskListener)
	 */
    @Override
	public synchronized void addProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers = proverTaskObservers.prepend(observer);
    }

    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#removeProverTaskObserver(de.uka.ilkd.key.prover.ProverTaskListener)
	 */
    @Override
	public synchronized void removeProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers = proverTaskObservers.removeAll(observer);
    }


    private class ProofListener implements RuleAppListener {

        /** invoked when a rule has been applied */
        public void ruleApplied(ProofEvent e) {
            if (!isAutoModeActive()) {
                return;
            }
            RuleAppInfo rai = e.getRuleAppInfo();
            if (rai == null) {
                return;
            }

            final GoalChooser goalChooser = getGoalChooserForProof(rai.getOriginalNode().proof());

            synchronized (goalChooser) {
                goalChooser.updateGoalList(rai.getOriginalNode (), e.getNewGoals().reverse()); // reverse just to keep old order
            }
        }
    }

    private boolean isAutoModeActive() {
        return autoModeActive;
    }

    private void setAutoModeActive(boolean autoModeActive) {
        this.autoModeActive = autoModeActive;
    }

    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#clear()
	 */
    @Override
	public void clear(){
        final GoalChooser goalChooser = getGoalChooserForProof(proof);
        proof = null;
        if(goalChooser != null) {
            goalChooser.init(null, ImmutableSLList.<Goal>nil());
        }
    }

    /* (non-Javadoc)
	 * @see de.uka.ilkd.key.prover.ProverCore#hasBeenInterrupted()
	 */
    @Override
	public boolean hasBeenInterrupted() {
        return cancelled;
    }
}
