package de.uka.ilkd.key.gui.interactionlog.algo;

import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.*;
import de.uka.ilkd.key.proof.Goal;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class Reapplication extends DefaultInteractionVisitor<Void> {
    private final Goal goal;

    public Reapplication(Goal goal) {
        this.goal = goal;
    }

    @Override
    protected Void defaultVisit(Interaction interaction) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Void visit(RuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(UseDependencyContractBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(AutoModeInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(MacroInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(UserNoteInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(OSSBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(SMTBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(PruneInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(LoopContractInternalBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(ContractBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(LoopInvariantBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(SettingChangeInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(MergeRuleBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }
}
