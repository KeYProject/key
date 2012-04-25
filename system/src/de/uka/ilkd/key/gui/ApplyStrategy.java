// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//




/*

Uses code by Hans Muller and Kathy Walrath from
http://java.sun.com/products/jfc/tsc/articles/threads/threads2.html

 */


package de.uka.ilkd.key.gui;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.proofevent.NodeReplacement;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;

/**
 * Applies rules in an automated fashion.
 * The caller should ensure that the strategy runs in its one thread
 */
public class ApplyStrategy {


    private static class SingleRuleApplicationInfo {

        static final SingleRuleApplicationInfo SUCCESS = new SingleRuleApplicationInfo() {
            public boolean isSuccess() {
                return true;
            }
        };

        private final String message;
        private final Goal nonCloseableGoal;

        private SingleRuleApplicationInfo() {
            message = "Rule applied successful";
            nonCloseableGoal = null;
        }

        SingleRuleApplicationInfo(String message, Goal nonCloseableGoal) {
            this.message = message;
            this.nonCloseableGoal = nonCloseableGoal;            
        }


        public boolean isSuccess() {
            return false;
        }

        public Goal getGoal() {
            return nonCloseableGoal;
        }

        public String message() {
            return message;
        }

    }

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
            sb.append("\n Message: " + message);
            sb.append("\n Error:" + isError());
            if (isError()) {
                sb.append("\n "+error.getMessage());
            }
            sb.append("\n Applied Rules: "+appliedRuleAppsCount);
            sb.append("\n Time: "+time);
            sb.append("\n Closed Goals: "+nrClosedGoals);
            return sb.toString();
        }

    }

    private static final String PROCESSING_STRATEGY = "Processing Strategy";

    /** the proof that is worked with */ 
    private Proof proof;
    /** the maximum of allowed rule applications */
    private int maxApplications;

    /** chooses goals to which rules are applied*/
    private IGoalChooser goalChooser;

    /** number of rules automatically applied */
    private int countApplied = 0;
    private long time;

    /** interrupted by the user? */
    private boolean autoModeActive = false;

    private List<ProverTaskListener> proverTaskObservers = new ArrayList<ProverTaskListener> ();

    /** time in ms after which rule application shall be aborted, -1 disables timeout */
    private long timeout = -1;

    private boolean stopAtFirstNonCloseableGoal;

    protected int closedGoals;


    // Please create this object beforehand and re-use it.
    // Otherwise the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(IGoalChooser goalChooser) {
        this.goalChooser = goalChooser;
    }

    /** applies rules that are chosen by the active strategy 
     * @return true iff a rule has been applied, false otherwise
     */
    private synchronized SingleRuleApplicationInfo applyAutomaticRule (boolean stopAtFirstNonClosableGoal) {
        // Look for the strategy ...
        RuleApp               app = null;
        Goal                  g;
        while ( ( g = goalChooser.getNextGoal () ) != null ) {                
            app = g.getRuleAppManager().next();
            //Hack: built in rules may become applicable without BuiltInRuleAppIndex noticing---->
            if(app == null) {
                g.ruleAppIndex().scanBuiltInRules(g);
                app = g.getRuleAppManager().next();
            }
            //<-------

            if (app == null) {        	
                if (stopAtFirstNonClosableGoal) {
                    return new SingleRuleApplicationInfo("Could not close goal.", g);      
                }
                goalChooser.removeGoal(g);
            } else {
                break;
            }
        }
         if (app == null) {          
            return new SingleRuleApplicationInfo("No more rules automatically applicable to any goal.", g);      
        } else {
            assert g != null;
            g.apply(app);
            return SingleRuleApplicationInfo.SUCCESS;
        }
    }


    /**
     * applies rules until this is no longer
     * possible or the thread is interrupted.
     */
    Object doWork() {
        time = System.currentTimeMillis();
        SingleRuleApplicationInfo srInfo = null;
        try{
            Debug.out("Strategy started.");
            boolean timeoutOrMaxSteps = maxRuleApplicationOrTimeoutExceeded();

            while (!timeoutOrMaxSteps) {     
                srInfo = applyAutomaticRule(stopAtFirstNonCloseableGoal); 
                if (!srInfo.isSuccess()) {                    
                    return new ApplyStrategyInfo(srInfo.message(), proof, null,
                            srInfo.getGoal(), System.currentTimeMillis()-time, countApplied, closedGoals);
                }
                countApplied++;
                fireTaskProgress ();
                if (Thread.interrupted()) { 
                    throw new InterruptedException();
                }                
                timeoutOrMaxSteps = maxRuleApplicationOrTimeoutExceeded();
            }
            if (timeoutOrMaxSteps) {
                return new ApplyStrategyInfo("Maximal number of rule applicatins reached or timed out.", proof, null, 
                        (Goal) null, System.currentTimeMillis()-time, countApplied, closedGoals);
            }
        } catch (InterruptedException e) {
            return new ApplyStrategyInfo("Interrupted.", proof, null, 
                    goalChooser.getNextGoal(), System.currentTimeMillis()-time, countApplied, closedGoals);
        } catch (Throwable t) { // treated later in finished()
            System.err.println(t);
            t.printStackTrace();
            return new ApplyStrategyInfo("Error.", proof, t, null, System.currentTimeMillis()-time, countApplied, closedGoals);
        } finally{
            time = System.currentTimeMillis()-time;
            Debug.out("Strategy stopped.");
            Debug.out("Applied ", countApplied);
            Debug.out("Time elapsed: ", time);
        }
        assert srInfo != null;
        return new ApplyStrategyInfo(srInfo.message(), proof, null, srInfo.getGoal(), time, countApplied, closedGoals);
    }


    /**
     * returns if the maximum number of rule applications or
     * the timeout has been reached
     * @return true if automatic rule application shall be stopped because the maximal
     * number of rules have been applied or the time out has been reached
     */
    private boolean maxRuleApplicationOrTimeoutExceeded() {
        return countApplied >= maxApplications ||
                timeout >= 0 && System.currentTimeMillis() - time >= timeout;
    }


    private synchronized void fireTaskStarted () {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            proverTaskObservers.get(i)
            .taskStarted(PROCESSING_STRATEGY, maxApplications);
        }
    }

    private synchronized void fireTaskProgress () {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            proverTaskObservers.get(i)
            .taskProgress(countApplied);
        }
    }

    private synchronized void fireTaskFinished (TaskFinishedInfo info) {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            proverTaskObservers.get(i).taskFinished(info);
        }
    }


    private void init(Proof newProof, ImmutableList<Goal> goals, int maxSteps, long timeout) {
        this.proof      = newProof;
        maxApplications = maxSteps;
        this.timeout    = timeout;
        countApplied    = 0; 
        closedGoals     = 0;        
        goalChooser.init ( newProof, goals );
        setAutoModeActive(true);

        fireTaskStarted ();
    }


    /* private KeYMediator mediator() {
        return medi;
    }
     */


    public ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals, int maxSteps, long timeout, boolean stopAtFirstNonCloseableGoal) {
        assert proof != null;

        this.stopAtFirstNonCloseableGoal = stopAtFirstNonCloseableGoal; 

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

        ProofListener pl = new ProofListener();
        Goal.addRuleAppListener( pl );        

        ApplyStrategyInfo result = null;
        try {  
            result = (ApplyStrategyInfo) doWork();
        } finally {
            proof.removeProofTreeListener(treeListener);
            Goal.removeRuleAppListener(pl);            
            setAutoModeActive(false);
        }

        if (result != null) {
            if (proof != null) { // Maybe the proof was removed from the proof list and #clear() has set the proof reference to null. It is possible because this statement is executed after MainWindow#frozen is set to false.
                proof.addAutoModeTime(result.getTime());
            }
            
            fireTaskFinished (new DefaultTaskFinishedInfo(this, result, 
                    proof, result.getTime(), 
                    result.getAppliedRuleApps(), result.getClosedGoals()));
        }

        return result;
    }


    public synchronized void addProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers.add(observer);
    }

    public synchronized void removeProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers.remove(observer);
    }


    private class ProofListener implements RuleAppListener {

        /** invoked when a rule has been applied */
        public void ruleApplied(ProofEvent e) {
            if (!isAutoModeActive() || e.getSource() != proof) return;            
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

                goalChooser.updateGoalList ( rai.getOriginalNode (), newGoals );
            }
        }
    }

    public boolean isAutoModeActive() {
        return autoModeActive;
    }

    public void setAutoModeActive(boolean autoModeActive) {
        this.autoModeActive = autoModeActive;
    }    

    /**Used by, e.g., {@code InteractiveProver.clear()} in order to prevent memory leaking. 
     * When a proof obligation is abandoned all references to the proof must be reset.
     * @author gladisch */
    public void clear(){
        proof = null;
        if(goalChooser!=null){
            goalChooser.init(null, ImmutableSLList.<Goal>nil());
        }
    }
}
