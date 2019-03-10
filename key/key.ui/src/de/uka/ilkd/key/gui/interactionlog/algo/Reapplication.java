package de.uka.ilkd.key.gui.interactionlog.algo;

import de.uka.ilkd.key.api.ProofMacroApi;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.*;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.RuleCommand;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.settings.ProofSettings;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class Reapplication extends DefaultInteractionVisitor<Void> {
    private final Goal goal;
    private WindowUserInterfaceControl uic;

    public Reapplication(Goal goal) {
        this.goal = goal;
    }

    @Override
    protected Void defaultVisit(Interaction interaction) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Void visit(RuleInteraction interaction) {
        RuleCommand ruleCommand = new RuleCommand();
        EngineState state = new EngineState(goal.proof());
        RuleCommand.Parameters parameter = null;
        try {
            parameter = ruleCommand.evaluateArguments(state, interaction.getArguments());
            ruleCommand.execute(uic, parameter, state);
        } catch (Exception e) {
            throw new IllegalStateException("Rule application", e);
        }
        return null;
    }

    @Override
    public Void visit(UseDependencyContractBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(AutoModeInteraction interaction) {
        uic.getProofControl().startAutoMode(goal.proof(), goal.proof().openGoals(), uic);
        return super.visit(interaction);
    }

    @Override
    public Void visit(MacroInteraction interaction) {
        ProofMacro macro = new ProofMacroApi().getMacro(interaction.getMacro());
        PosInOccurrence pio = interaction.getPos();
        if (macro != null) {
            if (!macro.canApplyTo(goal.node(), pio)) {
                throw new IllegalStateException("Macro not applicable");
            }

            try {
                macro.applyTo(uic, goal.node(), pio, uic);
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        return null;
    }

    @Override
    public Void visit(UserNoteInteraction interaction) {
        // weigl: maybe edit the change note feature here.
        return null;
    }

    @Override
    public Void visit(OSSBuiltInRuleInteraction interaction) {
        OneStepSimplifier oss = new OneStepSimplifier();
        PosInOccurrence pio = interaction.getOccurenceIdentifier().rebuildOn(goal);
        OneStepSimplifierRuleApp app = oss.createApp(pio, goal.proof().getServices());
        goal.apply(app);
        return null;
    }

    @Override
    public Void visit(SMTBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(PruneInteraction interaction) {
        Optional<Node> node = interaction.getNodeId().findNode(goal.proof());
        node.ifPresent(node1 -> goal.proof().pruneProof(node1));
        return null;
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
        ProofSettings settings = goal.proof().getSettings();

        switch (interaction.getType()) {
            case SMT:
                settings.getSMTSettings().readSettings(this, interaction.getSavedSettings());
                break;
            case CHOICE:
                settings.getChoiceSettings().readSettings(this, interaction.getSavedSettings());
                break;
            case STRATEGY:
                settings.getStrategySettings().readSettings(this, interaction.getSavedSettings());
                break;
        }

        return super.visit(interaction);

    }

    @Override
    public Void visit(MergeRuleBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }
}
