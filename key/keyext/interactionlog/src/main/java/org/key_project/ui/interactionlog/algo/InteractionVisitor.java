package org.key_project.ui.interactionlog.algo;

import org.key_project.ui.interactionlog.model.*;
import org.key_project.ui.interactionlog.model.builtin.*;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public interface InteractionVisitor<T> {
    T visit(RuleInteraction interaction);

    T visit(UseDependencyContractBuiltInRuleInteraction interaction);

    T visit(AutoModeInteraction interaction);

    T visit(MacroInteraction interaction);

    T visit(UserNoteInteraction interaction);

    T visit(OSSBuiltInRuleInteraction interaction);

    T visit(SMTBuiltInRuleInteraction interaction);

    T visit(PruneInteraction interaction);

    T visit(LoopContractInternalBuiltInRuleInteraction interaction);

    T visit(ContractBuiltInRuleInteraction interaction);

    T visit(LoopInvariantBuiltInRuleInteraction interaction);

    T visit(SettingChangeInteraction interaction);

    T visit(MergeRuleBuiltInRuleInteraction interaction);
}
