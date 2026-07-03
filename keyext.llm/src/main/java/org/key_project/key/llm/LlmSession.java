/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import org.key_project.key.llm.mcp.BuiltInMCPClient;
import org.key_project.key.llm.mcp.McpClient;

import java.net.URI;
import java.util.Set;
import java.util.TreeSet;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmSession {
    private final BuiltInMCPClient mcpClient;
    private String model = "azure.gpt-4.1-mini";
    private String apiEndpoint;
    private String authToken;
    private Set<URI> selectedFiles = new TreeSet<>();

    /// Initialize
    public static LlmSession createUsingSettings() {
        return new LlmSession(LlmSettings.INSTANCE.getApiEndpoint(),
                LlmSettings.INSTANCE.getAuthToken(),
                LlmSettings.INSTANCE.getDefaultModel());
    }

    public LlmSession(String apiEndpoint, String authToken, String model) {
        this.apiEndpoint = apiEndpoint;
        this.authToken = authToken;
        this.model = model;
        mcpClient = new BuiltInMCPClient();
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

    public McpClient getMcpClient() {
        return mcpClient;
    }
}
