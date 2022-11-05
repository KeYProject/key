package de.uka.ilkd.key.proof;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Interface for tracking new RuleApps
 */
public interface NewRuleListener {

    /**
     * Called when a new RuleApp is added
     */
    void ruleAdded(RuleApp rule, PosInOccurrence pos);

    /**
     * Called when a collection of new RuleApps is added
     */
    void rulesAdded(ImmutableList<? extends RuleApp> rule, PosInOccurrence pos);

}
