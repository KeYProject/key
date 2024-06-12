package org.key_project.ncore.rules;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.ncore.proof.ProofGoal;
import org.key_project.util.collection.ImmutableList;

public interface Rule extends Named {
    /**
     * the rule is applied on the given goal using the information of rule application.
     *
     * @param goal the Goal on which to apply <tt>ruleApp</tt>
     * @param ruleApp the rule application to be executed
     * @return all open goals below \old(goal.node()), i.e. the goals resulting from the rule
     *         application
     * @throws RuleAbortException when this rule was aborted
     */
    @NonNull
    <G extends ProofGoal> ImmutableList<G> apply(G goal, RuleApp ruleApp)
            throws RuleAbortException;

    /**
     * the name of the rule
     */
    Name name();

    /**
     * returns the display name of the rule
     */
    String displayName();
}
