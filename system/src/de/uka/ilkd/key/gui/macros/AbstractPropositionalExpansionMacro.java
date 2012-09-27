package de.uka.ilkd.key.gui.macros;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.InteractiveProver;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedRuleApplicationManager;

public abstract class AbstractPropositionalExpansionMacro implements ProofMacro {

    private static class StopListener implements ProverTaskListener {

        private final Goal goal;
        private final AutomatedRuleApplicationManager realManager;
        private final InteractiveProver interactiveProver;

        public StopListener(InteractiveProver interactiveProver, Goal goal, AutomatedRuleApplicationManager realManager) {
            this.interactiveProver = interactiveProver;
            this.goal = goal;
            this.realManager = realManager;
        }

        @Override
        public void taskStarted(String message, int size) {
        }

        @Override 
        public void taskProgress(int position) {
        }

        @Override 
        public void taskFinished(TaskFinishedInfo info) {
            goal.setRuleAppManager(realManager);
            interactiveProver.removeProverTaskListener(this);
        }
    }

    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new HashSet<String>(Arrays.asList(strings)));
    }

    @Override 
    public String getDescription() {
        return "Closer description";
    }
    
    protected abstract Set<String> getAdmittedRuleNames();

    @Override 
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return true;
    }

    @Override 
    public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        InteractiveProver interactiveProver = mediator.getInteractiveProver();
        Goal goal = mediator.getSelectedGoal();

        AutomatedRuleApplicationManager realManager = goal.getRuleAppManager();
        AutomatedRuleApplicationManager manager = realManager;
        if(posInOcc != null) {
            manager = new FocussedRuleApplicationManager(manager, goal, posInOcc);
        }

        manager = new FilterAppManager(manager, getAdmittedRuleNames());
        goal.setRuleAppManager (manager);

        interactiveProver.addProverTaskListener(
                new StopListener(interactiveProver, goal, realManager));

        interactiveProver.startAutoMode(
                ImmutableSLList.<Goal>nil().prepend(goal));
    }

    private static class FilterAppManager implements AutomatedRuleApplicationManager {

        private final Set<String> admittedRuleNames;
        private final AutomatedRuleApplicationManager delegate;

        public FilterAppManager(AutomatedRuleApplicationManager delegate,
                Set<String> admittedRuleNames) {
            this.delegate = delegate;
            this.admittedRuleNames = admittedRuleNames;
        }

        public void ruleAdded(RuleApp ruleApp, PosInOccurrence pos) {
            assert ruleApp.rule() != null : "the rule in a ruleapp should not be null";
            String name = ruleApp.rule().name().toString();
            if(admittedRuleNames.contains(name)) {
                delegate.ruleAdded(ruleApp, pos);
            }
        }

        public void clearCache() {
            delegate.clearCache();
        }

        public RuleApp peekNext() {
            return delegate.peekNext();
        }

        public RuleApp next() {
            return delegate.next();
        }

        public void setGoal(Goal p_goal) {
            delegate.setGoal(p_goal);
        }

        public AutomatedRuleApplicationManager copy() {
            return new FilterAppManager(delegate.copy(), admittedRuleNames);
        }

    }
}
