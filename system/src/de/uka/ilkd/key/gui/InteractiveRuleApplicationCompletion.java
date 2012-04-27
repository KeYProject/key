package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

public interface InteractiveRuleApplicationCompletion {

    public abstract IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced);

    public abstract boolean canComplete(IBuiltInRuleApp app);

}
