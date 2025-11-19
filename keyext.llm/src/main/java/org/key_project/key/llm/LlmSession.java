package org.key_project.key.llm;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmSession {
    private String apiEndpoint;
    private String authToken;

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
}
