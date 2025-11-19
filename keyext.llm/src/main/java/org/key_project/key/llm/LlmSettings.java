package org.key_project.key.llm;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmSettings extends AbstractPropertiesSettings {
    public static final LlmSettings INSTANCE = new LlmSettings();
    private static final String CATEGORY = "llm";

    private final PropertyEntry<String> authToken = createStringProperty("authToken", "");
    private final PropertyEntry<String> apiEndpoint = createStringProperty("apiEndpoint", "https://ki-toolbox.scc.kit.edu/v1");
    private final PropertyEntry<String> defaultModel = createStringProperty("defaultModel", "azure.gpt-4.1-mini");
    private final PropertyEntry<List<String>> availableModels = createStringListProperty("availableModels",
            "azure.gpt-4.1-mini,gpt-oss:120b,mixtral:8x22b,qwen3-vl:235b-a22b-instruct");


    public LlmSettings() {
        super(CATEGORY);
    }

    public LlmSettings(LlmSettings settings) {
        this();
        setAvailableModels(new ArrayList<>(settings.getAvailableModels()));
        setApiEndpoint(settings.getApiEndpoint());
        setAuthToken(settings.getAuthToken());
    }

    public String getApiEndpoint() {
        return apiEndpoint.get();
    }

    public void setApiEndpoint(String apiEndpoint) {
        this.apiEndpoint.set(apiEndpoint);
    }

    public String getAuthToken() {
        return authToken.get();
    }

    public void setAuthToken(String authToken) {
        this.authToken.set(authToken);
    }

    public List<String> getAvailableModels() {
        return availableModels.get();
    }

    public void setAvailableModels(List<String> availableModels) {
        this.availableModels.set(availableModels);
    }

    public String getDefaultModel() {
        return defaultModel.get();
    }

    public void setDefaultModel(String defaultModel) {
        this.defaultModel.set(defaultModel);
    }
}
