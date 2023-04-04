/**
 * rule application with specific information how and where the rule has to be applied
 */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.collection.ImmutableList;

public interface RuleApp extends EqualsModProofIrrelevancy {

    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula) of this rule application
     */
    PosInOccurrence posInOccurrence();

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * @param goal the Goal where to apply the rule
     * @param services the Services encapsulating all java information
     * @return list of new created goals
     */
    ImmutableList<Goal> execute(Goal goal, Services services);

    /**
     * returns true if all variables are instantiated
     *
     * @return true if all variables are instantiated
     */
    boolean complete();

}
