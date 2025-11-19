/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmSession {
    private String model = "azure.gpt-4.1-mini";
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

    public String getModel() {
        return model;
    }

    public void setModel(String model) {
        this.model = model;
    }
}
