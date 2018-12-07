package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.Settings;

import javax.swing.*;
import java.util.*;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 */
public class ScriptRecorderFacade {
    private static List<InteractionListeners> listeners = new ArrayList<>();
    private static Map<Proof, InteractionLog> instances = new HashMap<>();
    private static DefaultListModel<InteractionLog> loadedInteractionLogs = new DefaultListModel<>();

    public static InteractionLog get(Proof proof) {
        if (!instances.containsKey(proof)) {
            InteractionLog il = new InteractionLog(proof);
            loadedInteractionLogs.addElement(il);
            instances.put(proof, il);
        }
        return instances.get(proof);
    }

    public static ListModel<InteractionLog> getLoadedInteractionLogs() {
        return loadedInteractionLogs;
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

    public static void settingChanged(Proof proof, Settings settings, SettingChangeInteraction.SettingType type) {
        Properties p = new Properties();
        settings.writeSettings(p, p);
        SettingChangeInteraction sci = new SettingChangeInteraction(p, type);
        InteractionLog log = get(proof);
        log.getInteractions().add(sci);
        emit(sci);
    }

    public static void runPrune(Node node) {
        InteractionLog state = get(node.proof());
        PruneInteraction interaction = new PruneInteraction(node);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
        InteractionLog state = get(node.proof());
        MacroInteraction interaction = new MacroInteraction(node, macro, posInOcc, info);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void runBuiltIn(Goal goal, IBuiltInRuleApp app, BuiltInRule rule,
                                  PosInOccurrence pos, boolean forced) {
        InteractionLog state = get(goal.proof());
        NodeInteraction interaction = new BuiltInRuleInteraction(goal.node(), app, rule, pos);
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

    public static void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info) {
        InteractionLog state = get(proof);
        AutoModeInteraction interaction = new AutoModeInteraction(initialGoals, info);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void runRule(Goal goal, RuleApp app) {
        System.out.println(app);
        InteractionLog state = get(goal.proof());
        RuleInteraction interaction = (new RuleInteraction(
                goal.node().parent(), app));
        state.getInteractions().add(interaction);
        emit(interaction);
    }
}
