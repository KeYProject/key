/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import org.key_project.key.llm.mcp.BuiltInMCPClient;

import javax.swing.*;
import javax.swing.table.DefaultTableCellRenderer;
import java.awt.event.ActionEvent;
import java.util.ArrayList;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
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

        btnFetchModels = new JButton(new FetchModelsAction());

        txtApiBaseUrl =
                addTextField("API Base URL", model.getApiEndpoint(), "", model::setApiEndpoint);
        txtAuthToken = addTextField("Auth Token", model.getAuthToken(), "", model::setAuthToken);
        cboDefaultModel = addComboBox("Default model", "Select the default model",
                0,
                model::setDefaultModel,
                model.getAvailableModels().toArray(new String[0]));

        model.addPropertyChangeListener("availableModels", evt -> {
            var seq = model.getAvailableModels().toArray(new String[0]);
            final var cboModel = new DefaultComboBoxModel<>(seq);
            cboModel.setSelectedItem(cboDefaultModel.getSelectedItem());
            cboDefaultModel.setModel(cboModel);
        });

        selAvailableModels = addListBox("Available Models", "",
                model::setAvailableModels, model.getAvailableModels(), s -> s);

        addTitledComponent("test", btnFetchModels, "test");

        var mcpClient = new BuiltInMCPClient().getAllToolNames().stream().toList();
        var name = new Column<>("Name", String.class, (String s) -> s);
        var awR = new Column<>("AwR", Boolean.class,
                (String s) -> model.getAllowedToolsWithApproval().contains(s),
                (String s, Object value) -> {
                    if (value == Boolean.TRUE)
                        model.getAllowedToolsWithApproval().add(s);
                    else
                        model.getAllowedToolsWithApproval().remove(s);
                }
        );
        var awoR = new Column<>("AwoR", Boolean.class, (String s) -> model.getAllowedToolsWithoutApproval().contains(s),
                (String s, Object value) -> {
                    if (value == Boolean.TRUE)
                        model.getAllowedToolsWithoutApproval().add(s);
                    else
                        model.getAllowedToolsWithoutApproval().remove(s);
                }
        );
        selAvailableTools = addTableBox("Tools Models", "", mcpClient, name, awR, awoR);

        // Set checkbox editor for boolean columns
        selAvailableTools.setDefaultEditor(Boolean.class, new DefaultCellEditor(new JCheckBox()));

        // Set checkbox renderer for boolean columns
        selAvailableTools.setDefaultRenderer(Boolean.class, new DefaultTableCellRenderer() {
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
            var data = Util.httpGet(txtApiBaseUrl.getText() + "/openai/models", txtAuthToken.getText());
            if (data != null) {
                var seq = new ArrayList<String>(32);
                for (var model : data.getAsJsonArray("data")) {
                    seq.add(model.getAsJsonObject().get("id").getAsString());
                }
                selAvailableModels.clearSelection();
                var listModel = ((DefaultListModel<String>) selAvailableModels.getModel());
                listModel.clear();
                listModel.addAll(seq);
                cboDefaultModel.setSelectedItem(listModel.get(0));
                System.out.println(data);
            }
        }
    }
}
