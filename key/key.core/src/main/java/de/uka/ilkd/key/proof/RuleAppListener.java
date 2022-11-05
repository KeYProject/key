package de.uka.ilkd.key.proof;

/**
 * This listener is notified whenever a rule is applied in an ongoing proof.
 */
@FunctionalInterface
public interface RuleAppListener {

    /**
     * Invoked when a rule has been applied.
     *
     * @param e the proof event containing the rule application.
     */
    void ruleApplied(de.uka.ilkd.key.proof.ProofEvent e);
}
