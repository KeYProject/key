package org.key_project.key.llm;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.gui.settings.InvalidSettingsInputException;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.util.Collection;
import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
@KeYGuiExtension.Info(experimental = false, description = "LLM support for KeY")
public class LlmExtension implements KeYGuiExtension, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Settings, KeYGuiExtension.Startup, KeYGuiExtension.LeftPanel, KeYGuiExtension.MainMenu {
    private KeyAction actionStartLlmPromptForCurrentProof;
    private TabPanel uiPrompt;

    @Override
    public @NonNull List<Action> getContextActions(
            @NonNull KeYMediator mediator, @NonNull ContextMenuKind kind, @NonNull Object underlyingObject) {
        return List.of();
    }

    @Override
    public LlmSettingsProvider getSettings() {
        return new LlmSettingsProvider();
    }

    @Override
    public void preInit(MainWindow window, KeYMediator mediator) {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(LlmSettings.INSTANCE);
        actionStartLlmPromptForCurrentProof = new StartLlmPromptForCurrentProofAction(window);
    }

    @Override
    public @NonNull List<Action> getMainMenuActions(@NonNull MainWindow mainWindow) {
        return List.of(actionStartLlmPromptForCurrentProof);
    }

    @Override
    public @NonNull Collection<TabPanel> getPanels(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        uiPrompt = new LlmPrompt(window,mediator);
        return List.of(uiPrompt);
    }

    public static class LlmSettingsProvider implements SettingsProvider {
        public static @Nullable LlmSettingsUI ui;

        @Override
        public String getDescription() {
            return "LLM Settings";
        }

        @Override
        public JPanel getPanel(MainWindow window) {
            return ui = new LlmSettingsUI(LlmSettings.INSTANCE);
        }

        @Override
        public void applySettings(MainWindow window) throws InvalidSettingsInputException {
            LlmSettings.INSTANCE.setApiEndpoint(ui.getModel().getApiEndpoint());
            LlmSettings.INSTANCE.setDefaultModel(ui.getModel().getDefaultModel());
            LlmSettings.INSTANCE.setAuthToken(ui.getModel().getAuthToken());
            LlmSettings.INSTANCE.setAvailableModels(ui.getModel().getAvailableModels());
        }
    }

}


/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
class StartLlmPromptForCurrentProofAction extends MainWindowAction {
    protected StartLlmPromptForCurrentProofAction(MainWindow mainWindow) {
        super(mainWindow, true);

        setName("Open LLM prompt");
        setMenuPath("Proof.LLM");
        KeyStrokeManager.get(this, "ctrl P");
        setAcceleratorLetter('L');
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        var proof = mainWindow.getMediator().getSelectedProof();


    }
}
