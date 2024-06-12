package org.key_project.ncore.rules;

import org.jspecify.annotations.Nullable;
import org.key_project.ncore.proof.ProofGoal;
import org.key_project.util.collection.ImmutableList;

public interface RuleApp {
    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * @param goal the Goal where to apply the rule
     * @return list of new created goals
     */
    @Nullable
    <G extends ProofGoal> ImmutableList<G> execute(G goal);

    /**
     * returns true if all variables are instantiated
     *
     * @return true if all variables are instantiated
     */
    boolean complete();

    /**
     * @return user-friendly name for this rule-application
     */
    default String displayName() {
        return rule().displayName();
    }

}
