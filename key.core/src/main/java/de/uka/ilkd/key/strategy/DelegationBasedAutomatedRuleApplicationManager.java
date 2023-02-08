package de.uka.ilkd.key.strategy;

/**
 * An {@link AutomatedRuleApplicationManager} based on delegation.
 *
 * @author Dominic Steinhoefel
 */
public interface DelegationBasedAutomatedRuleApplicationManager
        extends AutomatedRuleApplicationManager {
    /**
     * @return The delegate.
     */
    AutomatedRuleApplicationManager getDelegate();
}
