/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.settings.SettingsPanel;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Arrays;

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

                /*

  "data": [
    {
      "id": "kit.gpt-oss-120b",
      "name": "kit.gpt-oss-120b",
      "owned_by": "openai",
      "openai": {
        "id": "kit.gpt-oss-120b",
        "name": "kit.gpt-oss-120b",
        "owned_by": "openai",
        "openai": {
          "id": "kit.gpt-oss-120b"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.qwen3-reranker-8b",
      "name": "kit.qwen3-reranker-8b",
      "owned_by": "openai",
      "openai": {
        "id": "kit.qwen3-reranker-8b",
        "name": "kit.qwen3-reranker-8b",
        "owned_by": "openai",
        "openai": {
          "id": "kit.qwen3-reranker-8b"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.qwen3-embedding-8b",
      "name": "kit.qwen3-embedding-8b",
      "owned_by": "openai",
      "openai": {
        "id": "kit.qwen3-embedding-8b",
        "name": "kit.qwen3-embedding-8b",
        "owned_by": "openai",
        "openai": {
          "id": "kit.qwen3-embedding-8b"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.qwen3.5-397b-A17b",
      "name": "kit.qwen3.5-397b-A17b",
      "owned_by": "openai",
      "openai": {
        "id": "kit.qwen3.5-397b-A17b",
        "name": "kit.qwen3.5-397b-A17b",
        "owned_by": "openai",
        "openai": {
          "id": "kit.qwen3.5-397b-A17b"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.mistral-small-4-119b-a8b",
      "name": "kit.mistral-small-4-119b-a8b",
      "owned_by": "openai",
      "openai": {
        "id": "kit.mistral-small-4-119b-a8b",
        "name": "kit.mistral-small-4-119b-a8b",
        "owned_by": "openai",
        "openai": {
          "id": "kit.mistral-small-4-119b-a8b"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.minimax-m2.7-229b",
      "name": "kit.minimax-m2.7-229b",
      "owned_by": "openai",
      "openai": {
        "id": "kit.minimax-m2.7-229b",
        "name": "kit.minimax-m2.7-229b",
        "owned_by": "openai",
        "openai": {
          "id": "kit.minimax-m2.7-229b"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.gemma4-31b-it",
      "name": "kit.gemma4-31b-it",
      "owned_by": "openai",
      "openai": {
        "id": "kit.gemma4-31b-it",
        "name": "kit.gemma4-31b-it",
        "owned_by": "openai",
        "openai": {
          "id": "kit.gemma4-31b-it"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.flux.2-dev",
      "name": "kit.flux.2-dev",
      "owned_by": "openai",
      "openai": {
        "id": "kit.flux.2-dev",
        "name": "kit.flux.2-dev",
        "owned_by": "openai",
        "openai": {
          "id": "kit.flux.2-dev"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.voxtral-4b-tts-2603",
      "name": "kit.voxtral-4b-tts-2603",
      "owned_by": "openai",
      "openai": {
        "id": "kit.voxtral-4b-tts-2603",
        "name": "kit.voxtral-4b-tts-2603",
        "owned_by": "openai",
        "openai": {
          "id": "kit.voxtral-4b-tts-2603"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "kit.whisper-large-v3",
      "name": "kit.whisper-large-v3",
      "owned_by": "openai",
      "openai": {
        "id": "kit.whisper-large-v3",
        "name": "kit.whisper-large-v3",
        "owned_by": "openai",
        "openai": {
          "id": "kit.whisper-large-v3"
        },
        "urlIdx": 0,
        "connection_type": "local"
      },
      "urlIdx": 0,
      "connection_type": "local",
      "provider": ""
    },
    {
      "id": "azure.gpt-4.1",
      "name": "azure.gpt-4.1",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-4.1",
        "name": "azure.gpt-4.1",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-4.1"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-4.1-mini",
      "name": "azure.gpt-4.1-mini",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-4.1-mini",
        "name": "azure.gpt-4.1-mini",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-4.1-mini"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-4.1-nano",
      "name": "azure.gpt-4.1-nano",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-4.1-nano",
        "name": "azure.gpt-4.1-nano",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-4.1-nano"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.o3",
      "name": "azure.o3",
      "owned_by": "openai",
      "openai": {
        "id": "azure.o3",
        "name": "azure.o3",
        "owned_by": "openai",
        "openai": {
          "id": "azure.o3"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.o4-mini",
      "name": "azure.o4-mini",
      "owned_by": "openai",
      "openai": {
        "id": "azure.o4-mini",
        "name": "azure.o4-mini",
        "owned_by": "openai",
        "openai": {
          "id": "azure.o4-mini"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-5.1",
      "name": "azure.gpt-5.1",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-5.1",
        "name": "azure.gpt-5.1",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-5.1"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-5",
      "name": "azure.gpt-5",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-5",
        "name": "azure.gpt-5",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-5"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-5-mini",
      "name": "azure.gpt-5-mini",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-5-mini",
        "name": "azure.gpt-5-mini",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-5-mini"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-5-nano",
      "name": "azure.gpt-5-nano",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-5-nano",
        "name": "azure.gpt-5-nano",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-5-nano"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-5.4",
      "name": "azure.gpt-5.4",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-5.4",
        "name": "azure.gpt-5.4",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-5.4"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    },
    {
      "id": "azure.gpt-5.5",
      "name": "azure.gpt-5.5",
      "owned_by": "openai",
      "openai": {
        "id": "azure.gpt-5.5",
        "name": "azure.gpt-5.5",
        "owned_by": "openai",
        "openai": {
          "id": "azure.gpt-5.5"
        },
        "urlIdx": 1,
        "connection_type": "external"
      },
      "urlIdx": 1,
      "connection_type": "external",
      "provider": ""
    }
  ]
}
                 */
                System.out.println(data);
            }
        }
    }
}
