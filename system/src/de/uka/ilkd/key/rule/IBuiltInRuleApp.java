package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

public interface IBuiltInRuleApp extends RuleApp {

    /**
     * returns the built in rule of this rule application
     */
    BuiltInRule rule();

    /**
     * tries to complete the rule application from the available information
     * Attention: Do neither add GUI code to the rules nor use this method directly 
     * Instead ask the implementation of the {@link de.uka.ilkd.key.ui.UserInterface} to complete a built-in rule
     * For an example implementation see e.g. {@link UseOperationContractRule} or {@link UseDependencyContractRule}.    
     */
    IBuiltInRuleApp tryToInstantiate(Goal goal);

    /**
     * returns true if tryToInstantiate can complete the app
     * @return
     */
    boolean isSufficientlyComplete();
    
    ImmutableList<PosInOccurrence> ifInsts();

    IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts);

    IBuiltInRuleApp replacePos(PosInOccurrence newPos);

}
