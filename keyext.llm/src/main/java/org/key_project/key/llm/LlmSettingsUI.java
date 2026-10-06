/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.IntConsumer;
import java.util.function.IntSupplier;
import javax.swing.*;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.settings.SettingsPanel;

import org.key_project.key.llm.mcp.BuiltInMCPClient;

import net.miginfocom.layout.CC;

/**
 * Settings UI of the KeY LLM integration: connection, agent behavior, prompt/context budgets,
 * file handling, shell security and tool approval.
 *
 * @author Alexander Weigl
 */
public class LlmSettingsUI extends SettingsPanel {
    private final LlmSettings model;
    private final JTextField txtApiBaseUrl;
    private final JTextField txtAuthToken;
    private final JComboBox<String> cboDefaultModel;
    private final JList<String> selAvailableModels;
    private final JButton btnFetchModels;
    private final JTable selAvailableTools;

    public LlmSettingsUI(LlmSettings settings) {
        model = new LlmSettings(settings);

        addSeparator("Connection");
        txtApiBaseUrl = addTextField("API Base URL", model.getApiEndpoint(), "",
            model::setApiEndpoint);
        txtAuthToken = addTextField("Auth Token", model.getAuthToken(), "", model::setAuthToken);
        cboDefaultModel = addComboBox("Default model", "Select the default model", 0,
            model::setDefaultModel, model.getAvailableModels().toArray(new String[0]));

        model.addPropertyChangeListener("availableModels", evt -> {
            var seq = model.getAvailableModels().toArray(new String[0]);
            var cboModel = new DefaultComboBoxModel<>(seq);
            cboModel.setSelectedItem(cboDefaultModel.getSelectedItem());
            cboDefaultModel.setModel(cboModel);
        });

        selAvailableModels = addListBox("Available Models", "", model::setAvailableModels,
            model.getAvailableModels(), s -> s);

        btnFetchModels = new JButton(new FetchModelsAction());
        addTitledComponent("Model list", btnFetchModels,
            "Fetches the available models from the API base URL.");

        addSeparator("Agent behavior");
        addTextArea("System prompt", model.getSystemPrompt(),
            "The system prompt of the KeY-Agent (skills are appended while active).",
            model::setSystemPrompt);
        addCheckBox("Allow the agent to ask questions", "The agent may ask you a question "
            + "(ask_user). Questioning pauses the turn until you answer.",
            model.getAllowAgentQuestions(), model::setAllowAgentQuestions);
        addIntField("Max tool rounds",
            "Maximum number of tool-calling rounds in one agent turn.", model::getMaxToolRounds,
            model::setMaxToolRounds);
        addCheckBox("Send temperature", "Include a temperature value in requests.",
            model.getSendTemperature(), model::setSendTemperature);
        addDoubleField("Temperature", "", model::getTemperature, model::setTemperature);
        addCheckBox("Send max output tokens", "Cap the number of generated tokens per response.",
            model.getSendMaxOutputTokens(), model::setSendMaxOutputTokens);
        addIntField("Max output tokens", "", model::getMaxOutputTokens, model::setMaxOutputTokens);
        addCheckBox("Agent may use skills", "Give the agent a use_skill tool (default off).",
            model.getAgentCanUseSkills(), model::setAgentCanUseSkills);

        addSeparator("Context and history");
        addCheckBox("Attach proof context by default",
            "Whether a block describing the current proof state is attached to every prompt.",
            model.getAttachProofContext(), model::setAttachProofContext);
        addIntField("Max proof-context sequents", "", model::getProofContextMaxSequents,
            model::setProofContextMaxSequents);
        addIntField("Max proof-context chars", "", model::getProofContextMaxChars,
            model::setProofContextMaxChars);
        addIntField("Max history messages", "", model::getMaxHistoryMessages,
            model::setMaxHistoryMessages);
        addIntField("Max history chars", "", model::getMaxHistoryChars, model::setMaxHistoryChars);

        addSeparator("Files");
        addIntField("Max attached files", "", model::getMaxFileAttachments,
            model::setMaxFileAttachments);
        addIntField("Max file size (KB)", "", model::getMaxFileSizeKB, model::setMaxFileSizeKB);
        addIntField("Max file content chars", "", model::getMaxFileContentChars,
            model::setMaxFileContentChars);
        addIntField("Max model listing entries", "", model::getMaxModelListingEntries,
            model::setMaxModelListingEntries);

        addSeparator("Shell commands");
        addCheckBox("Enable shell commands (run_command)",
            "Whether the agent may run shell commands at all (approval is still required).",
            model.getShellEnabled(), model::setShellEnabled);
        addIntField("Shell timeout (seconds)", "", model::getShellTimeoutSeconds,
            model::setShellTimeoutSeconds);
        addIntField("Shell max output chars", "", model::getShellMaxOutputChars,
            model::setShellMaxOutputChars);
        addTextArea("Blocked shell patterns",
            String.join("\n", model.getShellBlockedPatterns()),
            "Regular expressions of commands that are refused regardless of approval; one per line.",
            s -> model.setShellBlockedPatterns(
                Arrays.stream(s.split("\n")).map(String::strip).filter(x -> !x.isBlank())
                        .toList()));

        addSeparator("Tools");
        var mcpClient = new BuiltInMCPClient().getAllToolNames().stream().toList();
        var name = new Column<String, String>("Name", String.class, s -> s);
        var disabled = new Column<String, Boolean>("Disabled", Boolean.class,
            model.getToolsDisabled()::contains,
            (s, value) -> {
                if (value == Boolean.TRUE) {
                    model.getToolsDisabled().add(s);
                } else {
                    model.getToolsDisabled().remove(s);
                }
            });
        var withApproval = new Column<String, Boolean>("With approval", Boolean.class,
            model.getAllowedToolsWithApproval()::contains,
            (s, value) -> {
                if (value == Boolean.TRUE) {
                    model.getAllowedToolsWithApproval().add(s);
                } else {
                    model.getAllowedToolsWithApproval().remove(s);
                }
            });
        var withoutApproval =
            new Column<String, Boolean>("Without approval (always)", Boolean.class,
                model.getAllowedToolsWithoutApproval()::contains,
                (s, value) -> {
                    if (value == Boolean.TRUE) {
                        model.getAllowedToolsWithoutApproval().add(s);
                    } else {
                        model.getAllowedToolsWithoutApproval().remove(s);
                    }
                });
        selAvailableTools = addTableBox("Tools", "Disable tools, or change their approval"
            + " behavior. Disabled tools are not sent to the model at all.", mcpClient, name,
            disabled, withApproval, withoutApproval);

        // Set checkbox editor and renderer for boolean columns
        selAvailableTools.setDefaultEditor(Boolean.class, new DefaultCellEditor(new JCheckBox()));
        selAvailableTools.setDefaultRenderer(Boolean.class,
            new javax.swing.table.DefaultTableCellRenderer() {
                @Override
                public java.awt.Component getTableCellRendererComponent(JTable table, Object value,
                        boolean isSelected, boolean hasFocus, int row, int column) {
                    JCheckBox checkBox = new JCheckBox();
                    if (value instanceof Boolean bool) {
                        checkBox.setSelected(bool);
                    }
                    checkBox.setHorizontalAlignment(JLabel.CENTER);
                    if (isSelected) {
                        checkBox.setBackground(table.getSelectionBackground());
                        checkBox.setForeground(table.getSelectionForeground());
                    } else {
                        checkBox.setBackground(table.getBackground());
                        checkBox.setForeground(table.getForeground());
                    }
                    return checkBox;
                }
            });

        addSeparator("User interface");
        addCheckBox("Auto-scroll output", "Automatically scroll to the newest messages.",
            model.getAutoScrollOutput(), model::setAutoScrollOutput);
        addCheckBox("Show tool activity", "Show a summary of tool calls in the conversation.",
            model.getShowToolActivity(), model::setShowToolActivity);

        addSeparator("Prompts & Skills");
        pCenter.add(new PromptLibraryEditor(), new CC().span(3).growX().wrap());
        pCenter.add(new SkillLibraryEditor(), new CC().span(3).growX().wrap());
    }

    /** Adds an integer spinner bound immediately to the settings model. */
    private void addIntField(String title, String info, IntSupplier get, IntConsumer set) {
        var spinner = new JSpinner(new SpinnerNumberModel(Math.max(0, get.getAsInt()), 0,
            Integer.MAX_VALUE, 1));
        addTitledComponent(title, spinner, info);
        spinner.addChangeListener(
            e -> set.accept(((Number) spinner.getValue()).intValue()));
    }

    /** Adds a double spinner bound immediately to the settings model. */
    private void addDoubleField(String title, String info, java.util.function.DoubleSupplier get,
            java.util.function.DoubleConsumer set) {
        var spinner = new JSpinner(new SpinnerNumberModel(Math.max(0, get.getAsDouble()), 0.0,
            2.0, 0.05));
        addTitledComponent(title, spinner, info);
        spinner.addChangeListener(
            e -> set.accept(((Number) spinner.getValue()).doubleValue()));
    }

    public LlmSettings getModel() {
        return model;
    }

    private class FetchModelsAction extends KeyAction {
        public FetchModelsAction() {
            setName("Fetch Models");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setEnabled(false);
            var worker = new SwingWorker<List<String>, Void>() {
                @Override
                protected List<String> doInBackground() throws Exception {
                    var data =
                        Util.httpGet(txtApiBaseUrl.getText() + "/openai/models",
                            txtAuthToken.getText());
                    var result = new ArrayList<String>(32);
                    if (data != null && data.has("data")) {
                        for (var model : data.getAsJsonArray("data")) {
                            result.add(model.getAsJsonObject().get("id").getAsString());
                        }
                    }
                    return result;
                }

                @Override
                protected void done() {
                    try {
                        var seq = resultNow();
                        if (seq.isEmpty()) {
                            JOptionPane.showMessageDialog(LlmSettingsUI.this,
                                "No models were returned.", "Fetch Models",
                                JOptionPane.WARNING_MESSAGE);
                            return;
                        }
                        selAvailableModels.clearSelection();
                        var listModel = (DefaultListModel<String>) selAvailableModels.getModel();
                        listModel.clear();
                        listModel.addAll(seq);
                        cboDefaultModel.setSelectedItem(listModel.get(0));
                        var sorted = new ArrayList<>(seq);
                        sorted.sort(String::compareTo);
                        model.setAvailableModels(sorted);
                    } catch (Exception ex) {
                        JOptionPane.showMessageDialog(LlmSettingsUI.this,
                            "Could not fetch models: " + ex.getMessage(), "Fetch Models",
                            JOptionPane.ERROR_MESSAGE);
                    } finally {
                        setEnabled(true);
                    }
                }
            };
            worker.execute();
        }
    }
}
