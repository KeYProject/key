package org.key_project.key.llm;

import java.net.URI;
import java.util.Set;
import java.util.TreeSet;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmSession {
    private String model = "azure.gpt-4.1-mini";
    private String apiEndpoint;
    private String authToken;
    private Set<URI> selectedFiles = new TreeSet<>();

    public LlmSession(String apiEndpoint, String authToken) {
        this.apiEndpoint = apiEndpoint;
        this.authToken = authToken;
    }

    public String getApiEndpoint() {
        return apiEndpoint;
    }

    public void setApiEndpoint(String apiEndpoint) {
        this.apiEndpoint = apiEndpoint;
    }

    public String getAuthToken() {
        return authToken;
    }

    public void setAuthToken(String authToken) {
        this.authToken = authToken;
    }

    public String getModel() {
        return model;
    }

    public void setModel(String model) {
        this.model = model;
    }

    public Set<URI> getSelectedFiles() {
        return selectedFiles;
    }

    public void setSelectedFiles(Set<URI> selectedFiles) {
        this.selectedFiles = selectedFiles;
    }
}
