package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * Instances of class implementing this interface are able to complete rule applications. At the moment they 
 * are only responsible for built-in rule apps, but they should be generalized to treat taclets as well.
 */
public interface InteractiveRuleApplicationCompletion {

    /**
     * method called to complete the given builtin rule application
     * @param app the app to complete
     * @param goal the goal where the app will be applied
     * @param forced a boolean indicating if the user shall be bothered if the instantiation is unique or
     * can be chosen in a reasonable way as if unique
     * @return the completed app or null if completion was not possible
     */
    public abstract IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced);

    /**
     * checks if this instance is responsible for the given app
     * @param app the rule app 
     * @return true iff this instance might be able to complete the app 
     */
    public abstract boolean canComplete(IBuiltInRuleApp app);

}
