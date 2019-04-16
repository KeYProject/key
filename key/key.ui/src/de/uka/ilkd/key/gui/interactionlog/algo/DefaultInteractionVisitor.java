package de.uka.ilkd.key.gui.interactionlog.algo;

import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.*;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class DefaultInteractionVisitor<T> implements InteractionVisitor<T> {
    protected T defaultVisit(Interaction interaction) {
        return null;
    }

    @Override
    public T visit(RuleInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(UseDependencyContractBuiltInRuleInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(AutoModeInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(MacroInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(UserNoteInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(OSSBuiltInRuleInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(SMTBuiltInRuleInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(PruneInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(LoopContractInternalBuiltInRuleInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(ContractBuiltInRuleInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(LoopInvariantBuiltInRuleInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(SettingChangeInteraction interaction) {
        return defaultVisit(interaction);
    }

    @Override
    public T visit(MergeRuleBuiltInRuleInteraction interaction) {
        return defaultVisit(interaction);
    }
}
