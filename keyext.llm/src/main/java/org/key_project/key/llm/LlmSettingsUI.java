package org.key_project.key.llm;

import de.uka.ilkd.key.gui.settings.SettingsPanel;

import javax.swing.*;

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

    public LlmSettingsUI(LlmSettings settings) {
        model = new LlmSettings(settings);

        txtApiBaseUrl = addTextField("API Base URL", model.getApiEndpoint(), "", model::setApiEndpoint);
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
    }

    public LlmSettings getModel() {
        return model;
    }
}
