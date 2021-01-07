package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedRuleApplicationManager;
import de.uka.ilkd.key.strategy.Strategy;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

// TODO: rules with no heuristics can not be executed even if they are in the addmittedRules set!
public class LimitedRulesMacro extends AbstractPropositionalExpansionMacro {
    private final int numSteps;
    private final Set<String> admittedRules;

    public LimitedRulesMacro(int numSteps, Set<String> admittedRules) {
        super();
        this.numSteps = numSteps;
        this.admittedRules = admittedRules;
    }

    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        if (goals == null || goals.isEmpty()) {
            // should not happen, because in this case canApplyTo returns
            // false
            return null;
        }

        final GoalChooser
            goalChooser = proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create();
        final ProverCore applyStrategy = new ApplyStrategy(goalChooser);
        final ImmutableList<Goal> ignoredOpenGoals =
            setDifference(proof.openGoals(), goals);

        //
        // The observer to handle the progress bar
        final ProofMacroListener pml =  new ProgressBarListener(goals.size(),
            getMaxSteps(proof), listener);
        applyStrategy.addProverTaskObserver(pml);
        // add a focus manager if there is a focus
        if(posInOcc != null && goals != null) {
            AutomatedRuleApplicationManager realManager = null;
            FocussedRuleApplicationManager manager = null;
            for (Goal goal: goals) {
                realManager = goal.getRuleAppManager();
                realManager.clearCache();
                manager = new FocussedRuleApplicationManager(realManager, goal, posInOcc);
                goal.setRuleAppManager(manager);
            }
        }

        // set a new strategy.
        Strategy oldStrategy = proof.getActiveStrategy();
        proof.setActiveStrategy(createStrategy(proof, posInOcc));

        ProofMacroFinishedInfo info =
            new ProofMacroFinishedInfo(this, goals, proof, false);
        try {
            // find the relevant goals
            // and start
            applyStrategy.start(proof, goals, numSteps, -1, false);
            synchronized(applyStrategy) { // wait for applyStrategy to finish its last rule application
                if(applyStrategy.hasBeenInterrupted()) { // reraise interrupted exception if necessary
                    throw new InterruptedException();
                }
            }
        } finally {
            // this resets the proof strategy and the managers after the automation
            // has run
            for (final Goal openGoal : proof.openGoals()) {
                AutomatedRuleApplicationManager manager = openGoal.getRuleAppManager();
                // touch the manager only if necessary
                if(manager instanceof FocussedRuleApplicationManager) {
                    manager = ((FocussedRuleApplicationManager) manager).rootManager;
                    manager.clearCache();
                    openGoal.setRuleAppManager(manager);
                }
            }
            final ImmutableList<Goal> resultingGoals =
                setDifference(proof.openGoals(), ignoredOpenGoals);
            info = new ProofMacroFinishedInfo(this, resultingGoals);
            proof.setActiveStrategy(oldStrategy);
            doPostProcessing(proof);
            applyStrategy.removeProverTaskObserver(pml);
        }
        return info;
    }

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return admittedRules;
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }

    @Override
    public String getName() {
        return "Propositional rules";
    }

    @Override
    public String getDescription() {
        return "This macro performs arbitrary propositional reasoning steps to close the goal.";
    }
}
