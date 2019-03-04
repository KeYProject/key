package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.BuiltInRuleInteraction;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.BuiltInRuleInteractionFactory;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.Settings;

import javax.swing.*;
import javax.xml.bind.JAXBException;
import java.io.File;
import java.util.*;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 */
public class InteractionRecorder implements InteractionListener, AutoModeListener {
    private List<InteractionRecorderListener> listeners = new ArrayList<>();
    private Map<Proof, InteractionLog> instances = new HashMap<>();
    private DefaultComboBoxModel<InteractionLog> loadedInteractionLogs = new DefaultComboBoxModel<>();

    private boolean disableAll = false;
    private boolean disableSettingsChanges = false;

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

    public InteractionLog readInteractionLog(File file) throws JAXBException {
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
        if (disableSettingsChanges) return;
        if (disableAll) return;

        Properties p = new Properties();
        settings.writeSettings(p, p);
        SettingChangeInteraction sci = new SettingChangeInteraction(p, type);
        if (message != null) sci.setMessage(message);
        InteractionLog log = get(proof);

        try {
            //Remove the last interaction if it was a change setting with the same type
            Interaction last = log.getInteractions().get(log.getInteractions().size() - 1);
            if (last instanceof SettingChangeInteraction) {
                SettingChangeInteraction change = (SettingChangeInteraction) last;
                if (change.getType() == type) {
                    log.getInteractions().remove(log.getInteractions().size() - 1);
                }
            }

        } catch (IndexOutOfBoundsException | NullPointerException ex) {
        }
        log.getInteractions().add(sci);
        emit(sci);
    }

    @Override
    public void runPrune(Node node) {
        if (disableAll) return;
        InteractionLog state = get(node.proof());
        PruneInteraction interaction = new PruneInteraction(node);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    @Override
    public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
        if (disableAll) return;
        InteractionLog state = get(node.proof());
        MacroInteraction interaction = new MacroInteraction(node, macro, posInOcc, info);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    @Override
    public void runBuiltInRule(Goal goal, IBuiltInRuleApp app, BuiltInRule rule,
                               PosInOccurrence pos, boolean forced) {
        if (disableAll) return;
        InteractionLog state = get(goal.proof());
        BuiltInRuleInteraction interaction = BuiltInRuleInteractionFactory.create(goal.node(), app);
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
        if (disableAll) return;
        InteractionLog state = get(proof);
        AutoModeInteraction interaction = new AutoModeInteraction(initialGoals, info);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    @Override
    public void runRule(Goal goal, RuleApp app) {
        if (disableAll) return;
        InteractionLog state = get(goal.proof());
        RuleInteraction interaction = (new RuleInteraction(
                goal.node(), app));
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    @Override
    public void autoModeStarted(ProofEvent e) {

    }

    @Override
    public void autoModeStopped(ProofEvent e) {

    }

    public boolean isDisableAll() {
        return disableAll;
    }

    public void setDisableAll(boolean disableAll) {
        this.disableAll = disableAll;
    }
}
