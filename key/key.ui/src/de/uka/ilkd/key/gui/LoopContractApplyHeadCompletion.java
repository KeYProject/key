package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopContractApplyHeadBuiltInRuleApp;

/**
 * Interactive completion for {@link LoopContractApplyHeadBuiltInRuleApp}.
 */
public class LoopContractApplyHeadCompletion
        implements InteractiveRuleApplicationCompletion {
    
    LoopContractApplyHeadCompletion(MainWindow mainWindow){ }

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp application,
            final Goal goal, final boolean force) {
        LoopContractApplyHeadBuiltInRuleApp result =
                (LoopContractApplyHeadBuiltInRuleApp) application;
        if (!result.complete() && result.cannotComplete(goal)) {
            return result;
        }
        
        result.tryToInstantiate(goal);
        return result;
    }

    @Override
    public boolean canComplete(final IBuiltInRuleApp app) {
        return app instanceof LoopContractApplyHeadBuiltInRuleApp;
    }
}
