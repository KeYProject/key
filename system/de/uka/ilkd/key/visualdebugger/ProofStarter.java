package de.uka.ilkd.key.visualdebugger;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.proofevent.IteratorOfNodeReplacement;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.util.ProgressMonitor;


/**
 * Starts and runs a proof attempt mostly separated from the rest of the KeY
 * system. It may be used for non-user visible sub proofs.
 */
public class ProofStarter {

    private IGoalChooser goalChooser;

    private int maxSteps = -1;

    private ProofOblInput po;

    private Proof proof;

    private Strategy strategy;

    private List progressMonitors = new LinkedList();

    private boolean useDecisionProcedures;
    
    /** creates an instance of this proof starter */
    public ProofStarter() {
        this.goalChooser = new DefaultGoalChooser();
        // for the moment to maintain old default
        useDecisionProcedures = true;
    }    
        
    /**
     * applies rules that are chosen by the active strategy
     * 
     * @return true iff a rule has been applied, false otherwise
     */
    private synchronized boolean applyAutomaticRule() {

        // Look for the strategy ...
        RuleApp app = null;
        Goal g;

        while ((g = goalChooser.getNextGoal()) != null) {

            app = g.getRuleAppManager().next();

            if (app == null)
                goalChooser.removeGoal(g);
            else
                break;
        }
        if (app == null)
            return false;

        if (g != null) {
            goalChooser.updateGoalList(g.node(), g.apply(app));
        }

        return true;
    }

 
    // - Note: This should be removed
    private void applySimplificationOnGoals(ListOfGoal goals, 
            BuiltInRule decisionProcedureRule) {
        if (goals.isEmpty()) {
            return;
        }
            
        final Proof p = goals.head().node().proof();

        final IteratorOfGoal i = goals.iterator();                      
        p.env().registerRule(decisionProcedureRule,
                de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);
        while (i.hasNext()) {
            final Goal g = i.next();
            final BuiltInRuleApp birApp = new BuiltInRuleApp(decisionProcedureRule, null, p
                    .getUserConstraint().getConstraint());
            g.apply(birApp);
        }
    }

    /**
     * returns the proof resulting from the proof attempt
     * 
     * @return the proof
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * initializes the proof starter, i.e. the proof is created and set up
     * 
     * @param po
     *                the ProofOblInput with the proof (proof attempt is only
     *                started on the first proof)
     */
    public void init(ProofOblInput po) {

        if (this.po != null) {
            throw new IllegalStateException("Proofstarter has been already"
                    + " instantiated.");
        }

        this.po = po;
        this.proof = po.getPO().getFirstProof();
    }

    /**
     * informs the registered progress monitors about the current progress (i.e. 
     * the number of rules applied until now)
     * @param progress the int counting the number of applied rules
     */
    private void informProgressMonitors(int progress) {
        final Iterator it = progressMonitors.iterator();
        while (it.hasNext()) {
            ((ProgressMonitor)it.next()).setProgress(progress);
        }        
    }

    /**
     * initialises the registered progress monitors with the maximal
     * steps to be performed
     * @param maxSteps an int indicating the maximal steps to be performed
     */
    private void initProgressMonitors(int maxSteps) {
        final Iterator it = progressMonitors.iterator();
        while (it.hasNext()) {
            ((ProgressMonitor)it.next()).setMaximum(maxSteps);
        }        
    }
    
    /**     
     * adds a progress monitor to the proof starter. The progress monitor will
     * be informed about the progress when performing a proof search. Therefore
     * its {@link ProgressMonitor#setMaximum(int)} will be called handing over the 
     * maximal number of rule steps to be performed before the proof attempt is stopped. 
     * After each rule application the monitor will receive a call to 
     * {@link ProgressMonitor#setProgress(int)} 
     * 
     * @param pm the ProgressMonitor to be added
     */
    public void addProgressMonitor(ProgressMonitor pm) {
        synchronized(progressMonitors) {
            if (!progressMonitors.contains(pm)) {
                progressMonitors.add(pm);
            }
        }
    }

    /**
     * removes <code>pm</code> from the list of progress monitor to be informed 
     * @param pm the ProgressMonitor to be removed
     */
    public void removeProgressMonitor(ProgressMonitor pm) {
        synchronized(progressMonitors) {
            progressMonitors.remove(pm);
        }
    }
    
    /**
     * starts a proof attempt
     * @param env the ProofEnvironment to which the proof object will be registered
     * @return <code>true</code> if the proof attempt terminated normally (i.e. no error has occured).
     * In particular <code>true</code> does <em>not</em> mean that the proof has been closed.
     */
    public boolean run(ProofEnvironment env) {
        if (proof == null) {
            throw new IllegalStateException(
                    "Proofstarter must be initialized before.");
        }

        final Strategy oldStrategy = proof.getActiveStrategy();
        if (strategy == null) {
            // in this case take the strategy of the proof settings
            setStrategy(proof.getActiveStrategy());
        } else {
            proof.setActiveStrategy(strategy);
        }
        if (maxSteps == -1) {
            // take default settings
            setMaxSteps(proof.getSettings().getStrategySettings().getMaxSteps());
        }

        final BuiltInRule decisionProcedureRule;
        if (useDecisionProcedures) {
            decisionProcedureRule = findSimplifyRule();
        } else {
            decisionProcedureRule = null;
        }

        env.registerProof(po, po.getPO());

        goalChooser.init(proof, proof.openGoals());
        final ProofListener pl = new ProofListener();

        Goal.addRuleAppListener(pl);
        
        try {

            int countApplied = 0;
            synchronized (progressMonitors) {
                initProgressMonitors(maxSteps);
                while (countApplied < maxSteps && applyAutomaticRule()) {
                    countApplied++;
                    informProgressMonitors(countApplied);
                }
            }
            if (useDecisionProcedures && decisionProcedureRule != null) {
                applySimplificationOnGoals(proof.openGoals(), decisionProcedureRule);
            }            
        } catch (Throwable e) {
            System.err.println(e);
            e.printStackTrace();
            return false;
        } finally {
            Goal.removeRuleAppListener(pl);
            env.removeProofList(po.getPO());
            proof.setActiveStrategy(oldStrategy);
        }

        return true;
    }


    /**
     * returns the decision procedure rule invoking simplify, if available otherwise null
     * is returned
     * @return the decision procedure calling Simplify or null if none has been found
     */
    private BuiltInRule findSimplifyRule() {
        BuiltInRule decisionProcedureRule = null;
        final IteratorOfBuiltInRule builtinRules = 
            proof.getSettings().getProfile().getStandardRules().getStandardBuiltInRules().iterator();
        while (builtinRules.hasNext()) {
            final BuiltInRule bir = builtinRules.next();
            if (bir instanceof SimplifyIntegerRule) {
                decisionProcedureRule = bir;
                break;
            }
        }
        return decisionProcedureRule;
    }


    /**
     * sets the maximal amount of steps to be performed
     * 
     * @param maxSteps
     *                the int limiting the maximal amount of steps done in
     *                automatic proof mode
     * @throws an
     *                 IllegalArgumentException if <tt>maxSteps</tt> is lesser
     *                 than zero
     */
    public void setMaxSteps(int maxSteps) {
        if (maxSteps < 0) {
            throw new IllegalArgumentException("Number of maximal proof"
                    + " steps must be zero or positive.");
        }
        this.maxSteps = maxSteps;
    }

    /**
     * sets the strategy to be used for the prove attempt
     * 
     * @param strategy
     *                the Strategy to use
     */
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    private class ProofListener implements RuleAppListener {

        /** invoked when a rule has been applied */
        public void ruleApplied(ProofEvent e) {
            if (e.getSource() != proof)
                return;

            RuleAppInfo rai = e.getRuleAppInfo();
            if (rai == null)
                return;

            synchronized (ProofStarter.this) {
                ListOfGoal newGoals = SLListOfGoal.EMPTY_LIST;
                IteratorOfNodeReplacement it = rai.getReplacementNodes();
                Node node;
                Goal goal;

                while (it.hasNext()) {
                    node = it.next().getNode();
                    goal = proof.getGoal(node);
                    if (goal != null)
                        newGoals = newGoals.prepend(goal);
                }

                goalChooser.updateGoalList(rai.getOriginalNode(), newGoals);
            }
        }

    }

    /**
     * if activated the proof starter will run decision procedures on all open goals
     * after the normal proof search has stopped.  
     * @param useDecisionProcedures the boolean if <tt>true</tt> activates otherwise disables 
     * running the decision procedures  
     */
    public void setUseDecisionProcedure(boolean useDecisionProcedures) {
       this.useDecisionProcedures = useDecisionProcedures;
    }

}
