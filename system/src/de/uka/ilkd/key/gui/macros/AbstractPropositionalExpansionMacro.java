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

/**
 * The Class AbstractPropositionalExpansionMacro applies purely propositional
 * rules.
 * 
 * The names of the set of rules to be applied is defined by the abstract method
 * {@link #getAdmittedRuleNames()}.
 * 
 * This is very helpful to perform many "andLeft", "impRight" or even "andRight"
 * steps at a time.
 * 
 * @author mattias ulbrich
 */
public abstract class AbstractPropositionalExpansionMacro implements ProofMacro {

    /**
     * When a prove run is finished, we need to reset the goals' rule
     * application managers using this listener.
     */
    private static class StopListener implements ProverTaskListener {

        private final InteractiveProver interactiveProver;

        public StopListener(InteractiveProver interactiveProver) {
            this.interactiveProver = interactiveProver;
        }

        @Override
        public void taskStarted(String message, int size) {
        }

        @Override 
        public void taskProgress(int position) {
        }

        @Override 
        public void taskFinished(TaskFinishedInfo info) {
            for (final Goal goal : interactiveProver.getProof().openGoals()) {
                AutomatedRuleApplicationManager manager = goal.getRuleAppManager();
                while(manager.getDelegate() != null) {
                    manager = manager.getDelegate();
                }
                manager.clearCache();
                goal.setRuleAppManager(manager);
            }
            interactiveProver.removeProverTaskListener(this);
        }
    }

    /*
     * convert a string array to a set of strings 
     */
    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new HashSet<String>(Arrays.asList(strings)));
    }

    /**
     * Gets the set of admitted rule names.
     * 
     * @return a constant non-<code>null</code> set
     */
    protected abstract Set<String> getAdmittedRuleNames();

    /** 
     * {@inheritDoc}
     * 
     * This macro can always be applied (does not change anything perhaps)
     * 
     * TODO make this only applicable if it has an impact.
     * 
     */
    @Override 
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return true;
    }

    /*
     * Set a new rule app manager similar to the focussed mode.
     * Then run automation mode and in the end reset the managers.
     */
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

        interactiveProver.addProverTaskListener(new StopListener(interactiveProver));

        interactiveProver.startAutoMode(
                ImmutableSLList.<Goal>nil().prepend(goal));
    }

    /**
     * The Class FilterAppManager is a special rule app manager which filters
     * the rule applications by taclet name.
     */
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
//                System.err.println("Accepted rule: " + name);
            } else {
//                System.err.println("Rejected rule: " + name);
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

        public AutomatedRuleApplicationManager getDelegate() {
            return delegate;
        }

    }
}
