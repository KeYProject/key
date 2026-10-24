/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.net.URI;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.key.llm.mcp.BuiltInMCPClient;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.TurnScheduler.ToolObserver;

import org.jspecify.annotations.Nullable;

/**
 * Per-proof LLM session: endpoint/model/auth configuration, selected files, the per-proof
 * conversation history and UI state (active skill, proof-context toggle), plus the turn machinery
 * ({@link TurnQueue}, background jobs and the lazy {@link TurnScheduler}) that lets the user
 * always enter messages and put running tools into the background.
 *
 * @author Alexander Weigl
 */
public class LlmSession {
    private final BuiltInMCPClient mcpClient;
    private final LlmContext context = new LlmContext();
    private final SubagentLog subagentLog = new SubagentLog();
    private final TurnQueue turnQueue = new TurnQueue();
    private final BackgroundJobRegistry backgroundJobs = new BackgroundJobRegistry(turnQueue);
    private final KeYAgentTools builtInTools = new KeYAgentTools();
    private @Nullable TurnScheduler turnScheduler;
    private @Nullable ToolObserver turnObserver;
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

    /**
     * Bounded record of sub-agent runs of this session (role, mode, per-task outcomes), consulted
     * by the {@code get_subagent_logs} tool and rendered in the tool-activity summary.
     */
    public SubagentLog getSubagentLog() {
        return subagentLog;
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

    // ------------------------------------------------------------------ turn machinery

    /** The FIFO queue of everything that drives a turn (user prompts, answers, tool outputs). */
    public TurnQueue getTurnQueue() {
        return turnQueue;
    }

    /** The running background tool calls of this session. */
    public BackgroundJobRegistry getBackgroundJobs() {
        return backgroundJobs;
    }

    /** The shared tool dispatcher (pool + dispatch lock) used by all loops of all sessions. */
    public ToolDispatcher getToolDispatcher() {
        return ToolDispatcher.INSTANCE;
    }

    /**
     * The lazy per-session turn scheduler. Creating it does not start its worker thread; that only
     * happens when {@link TurnScheduler#submitPrompt} is first called.
     */
    public synchronized TurnScheduler getTurnScheduler() {
        if (turnScheduler == null) {
            turnScheduler = new TurnScheduler(this, new DefaultChatCompletionsClient());
        }
        return turnScheduler;
    }

    /** Registers the observer receiving tool-lifecycle events from agent loops. */
    public void setTurnObserver(@Nullable ToolObserver observer) {
        this.turnObserver = observer;
    }

    /** The current tool-lifecycle observer (set by the session's {@link TurnScheduler}). */
    public @Nullable ToolObserver getTurnObserver() {
        return turnObserver;
    }

    /**
     * Whether the tool may be moved into the background: the per-tool user overrides (settings)
     * win, otherwise the tool's category/background metadata applies.
     */
    public boolean isBackgroundAllowed(String toolName) {
        boolean metadataDefault = false;
        try {
            metadataDefault = builtInTools.agent(toolName).backgroundable();
        } catch (Exception e) {
            // unknown tool: fall back to the settings-only answer
        }
        return LlmSettings.INSTANCE.isBackgroundAllowed(toolName, metadataDefault);
    }

    /** Queues a user prompt for the (lazily started) turn scheduler of this session. */
    public void submitUserPrompt(String text, @Nullable Proof proof, @Nullable Node node,
            @Nullable Skill skill) {
        getTurnScheduler().submitPrompt(text, proof, node, skill);
    }
}
