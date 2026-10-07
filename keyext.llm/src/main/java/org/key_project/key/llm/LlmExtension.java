/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.event.ActionEvent;
import java.util.Collection;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.gui.settings.InvalidSettingsInputException;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * KeY GUI extension that provides the KeY-Agent chat panel and its settings.
 *
 * @author Alexander Weigl
 */
@KeYGuiExtension.Info(experimental = false, description = "LLM support for KeY")
public class LlmExtension implements KeYGuiExtension, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Settings, KeYGuiExtension.Startup, KeYGuiExtension.LeftPanel,
        KeYGuiExtension.MainMenu {
    private KeyAction actionStartLlmPromptForCurrentProof;
    private TabPanel uiPrompt;

    @Override
    public @NonNull List<Action> getContextActions(
            @NonNull KeYMediator mediator, @NonNull ContextMenuKind kind,
            @NonNull Object underlyingObject) {
        return List.of();
    }

    @Override
    public LlmSettingsProvider getSettings() {
        return LlmSettingsProvider.INSTANCE;
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
    public @NonNull Collection<TabPanel> getPanels(@NonNull MainWindow window,
            @NonNull KeYMediator mediator) {
        uiPrompt = new LlmPrompt(window, mediator);
        return List.of(uiPrompt);
    }

    public static class LlmSettingsProvider implements SettingsProvider {
        /**
         * The singleton registered in the settings manager. Node selection in the settings tree
         * matches providers by object identity, so the chat panel must open the dialog with these
         * exact instances.
         */
        public static final LlmSettingsProvider INSTANCE = new LlmSettingsProvider();

        /** Settings-tree node for the tool approval/disablement table. */
        public static final ToolsSettingsProvider TOOLS = new ToolsSettingsProvider();

        /** Settings-tree node for the prompt library editor. */
        public static final LibrarySettingsProvider PROMPT_LIBRARY =
            new LibrarySettingsProvider("Prompts", new PromptLibraryEditor());

        /** Settings-tree node for the skill library editor. */
        public static final LibrarySettingsProvider SKILL_LIBRARY =
            new LibrarySettingsProvider("Skills", new SkillLibraryEditor());

        public static @Nullable LlmSettingsUI ui;

        @Override
        public String getDescription() {
            return "LLM Settings";
        }

        @Override
        public List<SettingsProvider> getChildren() {
            return List.of(TOOLS, PROMPT_LIBRARY, SKILL_LIBRARY);
        }

        @Override
        public JPanel getPanel(MainWindow window) {
            return ui = new LlmSettingsUI(LlmSettings.INSTANCE);
        }

        @Override
        public void applySettings(MainWindow window) throws InvalidSettingsInputException {
            var source = ui.getModel();
            var target = LlmSettings.INSTANCE;
            target.setApiEndpoint(source.getApiEndpoint());
            target.setAuthToken(source.getAuthToken());
            target.setDefaultModel(source.getDefaultModel());
            target.setAvailableModels(new java.util.ArrayList<>(source.getAvailableModels()));
            target.setSystemPrompt(source.getSystemPrompt());
            target.setMaxToolRounds(source.getMaxToolRounds());
            target.setAllowAgentQuestions(source.getAllowAgentQuestions());
            target.setSendTemperature(source.getSendTemperature());
            target.setTemperature(source.getTemperature());
            target.setSendMaxOutputTokens(source.getSendMaxOutputTokens());
            target.setMaxOutputTokens(source.getMaxOutputTokens());
            target.setAgentCanUseSkills(source.getAgentCanUseSkills());
            target.setAttachProofContext(source.getAttachProofContext());
            target.setProofContextMaxSequents(source.getProofContextMaxSequents());
            target.setProofContextMaxChars(source.getProofContextMaxChars());
            target.setMaxHistoryMessages(source.getMaxHistoryMessages());
            target.setMaxHistoryChars(source.getMaxHistoryChars());
            target.setMaxFileAttachments(source.getMaxFileAttachments());
            target.setMaxFileSizeKB(source.getMaxFileSizeKB());
            target.setMaxFileContentChars(source.getMaxFileContentChars());
            target.setMaxModelListingEntries(source.getMaxModelListingEntries());
            target.setShellEnabled(source.getShellEnabled());
            target.setShellTimeoutSeconds(source.getShellTimeoutSeconds());
            target.setShellMaxOutputChars(source.getShellMaxOutputChars());
            target.setShellBlockedPatterns(
                new java.util.ArrayList<>(source.getShellBlockedPatterns()));
            target.setAutoScrollOutput(source.getAutoScrollOutput());
            target.setShowToolActivity(source.getShowToolActivity());
        }

        /**
         * Tree-leaf provider for a dedicated library editor ("Prompts" and "Skills" nodes). The
         * embedded editors persist to the file-backed libraries immediately on Save, so
         * {@link #applySettings(MainWindow)} is a no-op.
         */
        public static final class LibrarySettingsProvider implements SettingsProvider {
            private final String description;
            private final LibraryEditorPanel<?> editor;

            private LibrarySettingsProvider(String description, LibraryEditorPanel<?> editor) {
                this.description = description;
                this.editor = editor;
            }

            @Override
            public String getDescription() {
                return description;
            }

            @Override
            public JPanel getPanel(MainWindow window) {
                return editor;
            }

            @Override
            public void applySettings(MainWindow window) {
                // the editors persist immediately; nothing to apply here
            }
        }

        /**
         * Tree-leaf provider for the "Tools" node: the tool approval/disablement table. The panel
         * edits its own working copy of {@link LlmSettings}; applying writes only the tool sets,
         * the main "LLM Settings" panel owns the remaining fields.
         */
        public static final class ToolsSettingsProvider implements SettingsProvider {
            private final LlmToolsPanel ui =
                new LlmToolsPanel(new LlmSettings(LlmSettings.INSTANCE));

            @Override
            public String getDescription() {
                return "Tools";
            }

            @Override
            public JPanel getPanel(MainWindow window) {
                return ui;
            }

            @Override
            public void applySettings(MainWindow window) {
                var source = ui.getModel();
                var target = LlmSettings.INSTANCE;
                target.setToolsDisabled(new java.util.TreeSet<>(source.getToolsDisabled()));
                target.setAllowedToolsWithApproval(
                    new java.util.TreeSet<>(source.getAllowedToolsWithApproval()));
                target.setAllowedToolsWithoutApproval(
                    new java.util.TreeSet<>(source.getAllowedToolsWithoutApproval()));
            }
        }
    }
}


/**
 * Menu action that opens (and focuses) the KeY-Agent panel.
 */
class StartLlmPromptForCurrentProofAction extends MainWindowAction {
    protected StartLlmPromptForCurrentProofAction(MainWindow mainWindow) {
        super(mainWindow, true);

        setName("Open LLM prompt");
        setMenuPath("Proof.LLM");
        KeyStrokeManager.get(this, "ctrl P");
        setAcceleratorLetter('K');
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        DockingHelper.focus(mainWindow, LlmPrompt.class);
    }
}
