package de.uka.ilkd.key.util.script;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.Settings;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 */
public class ScriptRecorderFacade {
    private static List<InteractionListeners> listeners = new ArrayList<>();
    private static Map<Proof, ScriptRecorderState> instances = new HashMap<>();

    public static ScriptRecorderState get(Proof proof) {
        return instances.computeIfAbsent(proof, key ->
                new ScriptRecorderState(proof)
        );
    }

    public static void registerOnSettings(Proof proof) {
        proof.getSettings().getStrategySettings().addSettingsListener(
                (evt) -> settingChanged(proof,
                        proof.getSettings().getSMTSettings(),
                        SettingChangeInteraction.SettingType.STRATEGY)
        );

        proof.getSettings().getChoiceSettings().addSettingsListener(
                (evt) -> settingChanged(proof,
                        proof.getSettings().getChoiceSettings(),
                        SettingChangeInteraction.SettingType.CHOICE)
        );

        proof.getSettings().getSMTSettings().addSettingsListener(
                (evt) -> settingChanged(proof,
                        proof.getSettings().getSMTSettings(),
                        SettingChangeInteraction.SettingType.SMT)
        );
    }

    public static void settingChanged(Proof proof,
                                      Settings settings,
                                      SettingChangeInteraction.SettingType type) {
        Properties p = new Properties();
        settings.writeSettings(p, p);

        SettingChangeInteraction sci = new SettingChangeInteraction(p, type);
        //TODO
        emit(sci);
    }

    public static void runPrune(Node node) {
        ScriptRecorderState state = get(node.proof());
        PruneInteraction interaction = new PruneInteraction(node);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
        ScriptRecorderState state = get(node.proof());
        MacroInteraction interaction = new MacroInteraction(node, macro, posInOcc, info);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void runBuiltIn(Goal goal, BuiltInRule rule, PosInOccurrence pos, boolean forced) {
        ScriptRecorderState state = get(goal.proof());
        NodeInteraction interaction = new BuiltInRuleInteraction(goal.node(), rule, pos);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void addListener(InteractionListeners listener) {
        listeners.add(listener);
    }

    public static void removeListener(InteractionListeners listener) {
        listeners.remove(listener);
    }

    private static void emit(Interaction interaction) {
        listeners.forEach(l -> l.onInteraction(interaction));
    }

    public static void runAutoMode(Proof proof, ImmutableList<Goal> goals, ApplyStrategyInfo info) {
        ScriptRecorderState state = get(proof);
        goals.stream().forEach(g -> {
            AutoModeInteraction interaction = new AutoModeInteraction(g.node(), info);
            state.getInteractions().add(interaction);
            emit(interaction);
        });
    }

    public static void runRule(Goal goal, RuleApp app) {
        ScriptRecorderState state = get(goal.proof());
        RuleInteraction interaction = (new RuleInteraction(
                goal.node().parent(), app));
        state.getInteractions().add(interaction);
        emit(interaction);
    }
}
