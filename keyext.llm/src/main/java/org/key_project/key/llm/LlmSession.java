/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.net.URI;
import java.util.Set;
import java.util.TreeSet;

import org.key_project.key.llm.mcp.BuiltInMCPClient;

import org.jspecify.annotations.Nullable;

/**
 * Per-proof LLM session: endpoint/model/auth configuration, selected files, the per-proof
 * conversation history and UI state (active skill, proof-context toggle).
 *
 * @author Alexander Weigl
 */
public class LlmSession {
    private final BuiltInMCPClient mcpClient;
    private final LlmContext context = new LlmContext();
    private String model = KeYAgentPrompts.DEFAULT_MODEL;
    private String apiEndpoint;
    private String authToken;
    private Set<URI> selectedFiles = new TreeSet<>();
    private boolean attachProofContext = false;
    private @Nullable String activeSkill = null;

    /// Initialize from the global settings.
    public static LlmSession createUsingSettings() {
        return new LlmSession(LlmSettings.INSTANCE.getApiEndpoint(),
            LlmSettings.INSTANCE.getAuthToken(), LlmSettings.INSTANCE.getDefaultModel());
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

    public BuiltInMCPClient getMcpClient() {
        return mcpClient;
    }

    /** Per-proof conversation history. */
    public LlmContext getContext() {
        return context;
    }

    /** Whether the proof context block should be attached to the next prompt. */
    public boolean isAttachProofContext() {
        return attachProofContext;
    }

    public void setAttachProofContext(boolean attachProofContext) {
        this.attachProofContext = attachProofContext;
    }

    /** Name of the currently applied skill, or {@code null}. */
    public @Nullable String getActiveSkill() {
        return activeSkill;
    }

    public void setActiveSkill(@Nullable String activeSkill) {
        this.activeSkill = activeSkill;
    }
}
