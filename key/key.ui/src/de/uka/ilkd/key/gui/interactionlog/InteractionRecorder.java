package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentListener;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.Settings;

import javax.swing.*;
import java.io.File;
import java.io.IOException;
import java.util.*;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 */
public class InteractionRecorder implements InteractionListener {
    private List<InteractionRecorderListener> listeners = new ArrayList<>();
    private Map<Proof, InteractionLog> instances = new HashMap<>();
    private DefaultComboBoxModel<InteractionLog> loadedInteractionLogs = new DefaultComboBoxModel<>();

    public InteractionLog get(Proof proof) {
        if (!instances.containsKey(proof)) {
            InteractionLog il = new InteractionLog(proof);
            loadedInteractionLogs.addElement(il);
            instances.put(proof, il);
            registerOnSettings(proof);
            registerDisposeListener(proof);
            createInitialSettingsEntry(proof);
        }
        return instances.get(proof);
    }

    private void createInitialSettingsEntry(Proof proof) {
        settingChanged(proof,
                proof.getSettings().getStrategySettings(),
                SettingType.STRATEGY, "Initial Config");
        settingChanged(proof,
                proof.getSettings().getSMTSettings(),
                SettingType.SMT, "Initial Config");
        settingChanged(proof,
                proof.getSettings().getChoiceSettings(),
                SettingType.CHOICE, "Initial Config");
    }

    private void registerDisposeListener(Proof proof) {
        proof.getEnv().addProofEnvironmentListener(new ProofEnvironmentListener() {
            @Override
            public void proofRegistered(ProofEnvironmentEvent event) {

            }

            @Override
            public void proofUnregistered(ProofEnvironmentEvent event) {
                //TODO check how to find out wheteher proof was removed or a different instance
            }
        });
    }

    public ComboBoxModel<InteractionLog> getLoadedInteractionLogs() {
        return loadedInteractionLogs;
    }

    public InteractionLog readInteractionLog(File file) throws IOException {
        InteractionLog log = InteractionLogFacade.readInteractionLog(file);
        loadedInteractionLogs.addElement(log);
        return log;
    }

    public void registerOnSettings(Proof proof) {
        proof.getSettings().getStrategySettings().addSettingsListener(
                (evt) -> settingChanged(proof,
                        proof.getSettings().getStrategySettings(),
                        SettingType.STRATEGY, null)
        );

        proof.getSettings().getChoiceSettings().addSettingsListener(
                (evt) -> settingChanged(proof,
                        proof.getSettings().getChoiceSettings(),
                        SettingType.CHOICE, null)
        );

        proof.getSettings().getSMTSettings().addSettingsListener(
                (evt) -> settingChanged(proof,
                        proof.getSettings().getSMTSettings(),
                        SettingType.SMT, null)
        );
    }

    @Override
    public void settingChanged(Proof proof, Settings settings, SettingType type, String message) {
        Properties p = new Properties();
        settings.writeSettings(p, p);
        SettingChangeInteraction sci = new SettingChangeInteraction(p, type);
        if (message != null) sci.setMessage(message);
        InteractionLog log = get(proof);
        log.getInteractions().add(sci);
        emit(sci);
    }

    @Override
    public void runPrune(Node node) {
        InteractionLog state = get(node.proof());
        PruneInteraction interaction = new PruneInteraction(node);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    @Override
    public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
        InteractionLog state = get(node.proof());
        MacroInteraction interaction = new MacroInteraction(node, macro, posInOcc, info);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    @Override
    public void runBuiltInRule(Goal goal, IBuiltInRuleApp app, BuiltInRule rule,
                               PosInOccurrence pos, boolean forced) {
        InteractionLog state = get(goal.proof());
        NodeInteraction interaction = new BuiltInRuleInteraction(goal.node(), app, rule, pos);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public void addListener(InteractionRecorderListener listener) {
        listeners.add(listener);
    }

    public void removeListener(InteractionRecorderListener listener) {
        listeners.remove(listener);
    }

    protected void emit(Interaction interaction) {
        listeners.forEach(l -> l.onInteraction(interaction));
    }

    @Override
    public void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info) {
        InteractionLog state = get(proof);
        AutoModeInteraction interaction = new AutoModeInteraction(initialGoals, info);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    @Override
    public void runRule(Goal goal, RuleApp app) {
        InteractionLog state = get(goal.proof());
        RuleInteraction interaction = (new RuleInteraction(
                goal.node(), app));
        state.getInteractions().add(interaction);
        emit(interaction);
    }
}
