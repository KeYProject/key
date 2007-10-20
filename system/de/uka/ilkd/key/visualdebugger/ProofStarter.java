package de.uka.ilkd.key.visualdebugger;

import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.decproc.JavaDecisionProcedureTranslationFactory;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.proofevent.IteratorOfNodeReplacement;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SimplifyIntegerRule;
import de.uka.ilkd.key.strategy.Strategy;

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

    private final static BuiltInRule SIMPLIFY_RULE = new SimplifyIntegerRule(false,
            new JavaDecisionProcedureTranslationFactory());

    /** creates an instance of this proof starter */
    public ProofStarter() {
        this.goalChooser = new DefaultGoalChooser();
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

    public boolean applyRule(Goal g, RuleApp app, ProofEnvironment env) {
        if (proof == null) {
            throw new IllegalStateException(
                    "Proofstarter must be initialized before.");
        }

        if (strategy == null) {
            // in this case take the strategy of the proof settings
            setStrategy(proof.getActiveStrategy());
        }

        if (maxSteps == -1) {
            // take default settings
            setMaxSteps(proof.getSettings().getStrategySettings().getMaxSteps());
        }

        env.registerProof(po, po.getPO());

        goalChooser.init(proof, proof.openGoals());
        final ProofListener pl = new ProofListener();

        Goal.addRuleAppListener(pl);

        try {
            g.apply(app);

            VisualDebugger.print("ProofStarter: Applied rule ");
        } catch (Throwable e) {
            System.err.println(e);
            e.printStackTrace();
            return false;
        } finally {
            Goal.removeRuleAppListener(pl);
            env.removeProofList(po.getPO());
        }

        return true;
    }

    // - Note: This should be removed
    public void applySimplificationOnGoals(ListOfGoal goals) {
        if (goals.isEmpty()) {
            return;
        }
            
        final Proof p = goals.head().node().proof();
        
        if (p.getSettings().getDecisionProcedureSettings().useSimplify()) {
            final IteratorOfGoal i = goals.iterator();                      
            
            p.env().registerRule(SIMPLIFY_RULE,
                    de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);

            while (i.hasNext()) {
                final Goal g = i.next();
                final BuiltInRuleApp birApp = new BuiltInRuleApp(SIMPLIFY_RULE, null, p
                        .getUserConstraint().getConstraint());
                g.apply(birApp);
            }
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

   
    public boolean run(ProofEnvironment env) {
        if (proof == null) {
            throw new IllegalStateException(
                    "Proofstarter must be initialized before.");
        }

        if (strategy == null) {
            // in this case take the strategy of the proof settings
            setStrategy(proof.getActiveStrategy());
        }

        if (maxSteps == -1) {
            // take default settings
            setMaxSteps(proof.getSettings().getStrategySettings().getMaxSteps());
        }

        env.registerProof(po, po.getPO());

        goalChooser.init(proof, proof.openGoals());
        final ProofListener pl = new ProofListener();

        Goal.addRuleAppListener(pl);

        try {

            int countApplied = 0;
            while (countApplied < maxSteps && applyAutomaticRule()) {
                countApplied++;
            }
            applySimplificationOnGoals(proof.openGoals());
            VisualDebugger.print("ProofStarter: Applied " + countApplied
                    + " Rules");
        } catch (Throwable e) {
            System.err.println(e);
            e.printStackTrace();
            return false;
        } finally {
            Goal.removeRuleAppListener(pl);
            env.removeProofList(po.getPO());
        }

        return true;
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

}
