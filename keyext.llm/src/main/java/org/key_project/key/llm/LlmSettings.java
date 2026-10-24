/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

import org.jspecify.annotations.Nullable;

/**
 * Proof-independent settings of the KeY LLM integration. All values are backed by
 * {@link AbstractPropertiesSettings.PropertyEntry} instances and are therefore persisted in the
 * {@code [llm]} section of the personal key settings.
 *
 * @author Alexander Weigl
 */
public class LlmSettings extends AbstractPropertiesSettings {

    /** Default blocklist injected into {@code shellBlockedPatterns} on first use. */
    public static final List<String> DEFAULT_SHELL_BLOCKED_PATTERNS = List.of(
        "\\brm\\s+(-\\w+\\s+)*-rf?\\b", "\\bmkfs(\\.[a-zA-Z0-9]+)?\\b",
        "\\bdd\\b[^\\n]*\\bof=/dev/",
        "\\bshutdown\\b", "\\breboot\\b", "\\bhalt\\b", "\\bpoweroff\\b", "\\bsudo\\b",
        "\\bdoas\\b",
        "\\bsu\\s+-", "\\bpkexec\\b", "(curl|wget).*\\|\\s*(sh|bash|zsh)", "\\b:(\\s|{)+\\(\\)",
        "\\bchmod\\s+-R\\s+\\S*\\s+(/|/etc|/usr|/boot)");

    public static final LlmSettings INSTANCE = new LlmSettings();
    private static final String CATEGORY = "llm";

    private final PropertyEntry<String> authToken = createStringProperty("authToken", "");
    private final PropertyEntry<String> apiEndpoint =
        createStringProperty("apiEndpoint", "https://ki-toolbox.scc.kit.edu/v1");
    private final PropertyEntry<String> defaultModel =
        createStringProperty("defaultModel", KeYAgentPrompts.DEFAULT_MODEL);
    private final PropertyEntry<List<String>> availableModels =
        createStringListProperty("availableModels", KeYAgentPrompts.DEFAULT_AVAILABLE_MODELS);

    // --- agent behavior ---
    private final PropertyEntry<String> systemPrompt =
        createStringProperty("systemPrompt", KeYAgentPrompts.SYSTEM_PROMPT);
    private final PropertyEntry<Integer> maxToolRounds = createIntegerProperty("maxToolRounds", 8);
    private final PropertyEntry<Boolean> allowAgentQuestions =
        createBooleanProperty("allowAgentQuestions", true);
    private final PropertyEntry<Boolean> sendTemperature =
        createBooleanProperty("sendTemperature", false);
    private final PropertyEntry<Double> temperature = createDoubleProperty("temperature", 0.2);
    private final PropertyEntry<Boolean> sendMaxOutputTokens =
        createBooleanProperty("sendMaxOutputTokens", false);
    private final PropertyEntry<Integer> maxOutputTokens =
        createIntegerProperty("maxOutputTokens", 4096);
    private final PropertyEntry<Boolean> agentCanUseSkills =
        createBooleanProperty("agentCanUseSkills", false);
    /** Whether the agent may consult a fresh LLM instance ({@code ask_llm}). */
    private final PropertyEntry<Boolean> askLlmEnabled =
        createBooleanProperty("askLlmEnabled", true);

    // --- sub-agents ---
    private final PropertyEntry<Boolean> subagentsEnabled =
        createBooleanProperty("subagentsEnabled", false);
    private final PropertyEntry<Integer> maxSubagentTurns =
        createIntegerProperty("maxSubagentTurns", 8);
    private final PropertyEntry<Integer> maxSubagentDepth =
        createIntegerProperty("maxSubagentDepth", 2);
    private final PropertyEntry<Integer> maxParallelSubagents =
        createIntegerProperty("maxParallelSubagents", 4);

    // --- context & history ---
    private final PropertyEntry<Boolean> attachProofContext =
        createBooleanProperty("attachProofContext", false);
    private final PropertyEntry<Integer> proofContextMaxSequents =
        createIntegerProperty("proofContextMaxSequents", 3);
    private final PropertyEntry<Integer> proofContextMaxChars =
        createIntegerProperty("proofContextMaxChars", 8000);
    private final PropertyEntry<Integer> maxHistoryMessages =
        createIntegerProperty("maxHistoryMessages", 30);
    private final PropertyEntry<Integer> maxHistoryChars =
        createIntegerProperty("maxHistoryChars", 32000);

    // --- files ---
    private final PropertyEntry<Integer> maxFileAttachments =
        createIntegerProperty("maxFileAttachments", 10);
    private final PropertyEntry<Integer> maxFileSizeKB = createIntegerProperty("maxFileSizeKB", 64);
    private final PropertyEntry<Integer> maxFileContentChars =
        createIntegerProperty("maxFileContentChars", 8000);
    private final PropertyEntry<Integer> maxModelListingEntries =
        createIntegerProperty("maxModelListingEntries", 1000);

    // --- tools & security ---
    private final PropertyEntry<Boolean> shellEnabled = createBooleanProperty("shellEnabled", true);
    private final PropertyEntry<Integer> shellTimeoutSeconds =
        createIntegerProperty("shellTimeoutSeconds", 30);
    private final PropertyEntry<Integer> shellMaxOutputChars =
        createIntegerProperty("shellMaxOutputChars", 65536);
    private final PropertyEntry<List<String>> shellBlockedPatterns =
        createStringListProperty("shellBlockedPatterns",
            String.join(",", DEFAULT_SHELL_BLOCKED_PATTERNS));
    private final PropertyEntry<Set<String>> toolsDisabled =
        createStringSetProperty("toolsDisabled", new TreeSet<>());
    private final PropertyEntry<Set<String>> allowedToolsWithApproval =
        createStringSetProperty("allowedToolsWithApproval", new TreeSet<>());
    private final PropertyEntry<Set<String>> allowedToolsWithoutApproval =
        createStringSetProperty("allowedToolsWithoutApproval", new TreeSet<>());
    private final PropertyEntry<Set<String>> backgroundToolsEnabled =
        createStringSetProperty("backgroundToolsEnabled", new TreeSet<>());
    private final PropertyEntry<Set<String>> backgroundToolsDisabled =
        createStringSetProperty("backgroundToolsDisabled", new TreeSet<>());
    private final PropertyEntry<Integer> maxBackgroundJobs =
        createIntegerProperty("maxBackgroundJobs", 4);

    // --- prompt & skill libraries ---
    /**
     * Search path of the prompt library: the directories (in order) whose {@code <name>.md} files
     * hold the user-defined prompts. Empty means the default directory
     * {@code <key-config-dir>/llm/prompts}. Entries may use {@code ~} (home directory),
     * {@code $(pwd)} or relative paths (working directory).
     */
    private final PropertyEntry<List<String>> promptLibraryPaths =
        createStringListProperty("promptLibraryPaths", "");
    /** Search path of the skill library (see {@link #promptLibraryPaths}). */
    private final PropertyEntry<List<String>> skillLibraryPaths =
        createStringListProperty("skillLibraryPaths", "");

    // --- ui ---
    private final PropertyEntry<Boolean> autoScrollOutput =
        createBooleanProperty("autoScrollOutput", true);
    private final PropertyEntry<Boolean> showToolActivity =
        createBooleanProperty("showToolActivity", true);

    public LlmSettings() {
        super(CATEGORY);
    }

    /** Copy constructor; copies all persisted values from {@code other}. */
    public LlmSettings(LlmSettings other) {
        this();
        setApiEndpoint(other.getApiEndpoint());
        setAuthToken(other.getAuthToken());
        setDefaultModel(other.getDefaultModel());
        setAvailableModels(new ArrayList<>(other.getAvailableModels()));
        setSystemPrompt(other.getSystemPrompt());
        setMaxToolRounds(other.getMaxToolRounds());
        setAllowAgentQuestions(other.getAllowAgentQuestions());
        setSendTemperature(other.getSendTemperature());
        setTemperature(other.getTemperature());
        setSendMaxOutputTokens(other.getSendMaxOutputTokens());
        setMaxOutputTokens(other.getMaxOutputTokens());
        setAgentCanUseSkills(other.getAgentCanUseSkills());
        setAskLlmEnabled(other.getAskLlmEnabled());
        setSubagentsEnabled(other.getSubagentsEnabled());
        setMaxSubagentTurns(other.getMaxSubagentTurns());
        setMaxSubagentDepth(other.getMaxSubagentDepth());
        setMaxParallelSubagents(other.getMaxParallelSubagents());
        setAttachProofContext(other.getAttachProofContext());
        setProofContextMaxSequents(other.getProofContextMaxSequents());
        setProofContextMaxChars(other.getProofContextMaxChars());
        setMaxHistoryMessages(other.getMaxHistoryMessages());
        setMaxHistoryChars(other.getMaxHistoryChars());
        setMaxFileAttachments(other.getMaxFileAttachments());
        setMaxFileSizeKB(other.getMaxFileSizeKB());
        setMaxFileContentChars(other.getMaxFileContentChars());
        setMaxModelListingEntries(other.getMaxModelListingEntries());
        setShellEnabled(other.getShellEnabled());
        setShellTimeoutSeconds(other.getShellTimeoutSeconds());
        setShellMaxOutputChars(other.getShellMaxOutputChars());
        setShellBlockedPatterns(new ArrayList<>(other.getShellBlockedPatterns()));
        setToolsDisabled(new TreeSet<>(other.getToolsDisabled()));
        setAllowedToolsWithApproval(new TreeSet<>(other.getAllowedToolsWithApproval()));
        setAllowedToolsWithoutApproval(new TreeSet<>(other.getAllowedToolsWithoutApproval()));
        setBackgroundToolsEnabled(new TreeSet<>(other.getBackgroundToolsEnabled()));
        setBackgroundToolsDisabled(new TreeSet<>(other.getBackgroundToolsDisabled()));
        setMaxBackgroundJobs(other.getMaxBackgroundJobs());
        setPromptLibraryPaths(new ArrayList<>(other.getPromptLibraryPaths()));
        setSkillLibraryPaths(new ArrayList<>(other.getSkillLibraryPaths()));
        setAutoScrollOutput(other.getAutoScrollOutput());
        setShowToolActivity(other.getShowToolActivity());
    }

    // --- plain accessors ---

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

    // --- agent behavior ---

    public String getSystemPrompt() {
        return systemPrompt.get();
    }

    public void setSystemPrompt(String systemPrompt) {
        this.systemPrompt.set(systemPrompt);
    }

    public int getMaxToolRounds() {
        return maxToolRounds.get();
    }

    public void setMaxToolRounds(int maxToolRounds) {
        this.maxToolRounds.set(maxToolRounds);
    }

    public boolean getAllowAgentQuestions() {
        return allowAgentQuestions.get();
    }

    public void setAllowAgentQuestions(boolean allow) {
        this.allowAgentQuestions.set(allow);
    }

    public boolean getSendTemperature() {
        return sendTemperature.get();
    }

    public void setSendTemperature(boolean send) {
        this.sendTemperature.set(send);
    }

    public double getTemperature() {
        return temperature.get();
    }

    public void setTemperature(double temperature) {
        this.temperature.set(temperature);
    }

    public boolean getSendMaxOutputTokens() {
        return sendMaxOutputTokens.get();
    }

    public void setSendMaxOutputTokens(boolean send) {
        this.sendMaxOutputTokens.set(send);
    }

    public int getMaxOutputTokens() {
        return maxOutputTokens.get();
    }

    public void setMaxOutputTokens(int max) {
        this.maxOutputTokens.set(max);
    }

    public boolean getAgentCanUseSkills() {
        return agentCanUseSkills.get();
    }

    public void setAgentCanUseSkills(boolean v) {
        this.agentCanUseSkills.set(v);
    }

    /** Whether the agent may consult a fresh LLM instance via {@code ask_llm}. */
    public boolean getAskLlmEnabled() {
        return askLlmEnabled.get();
    }

    public void setAskLlmEnabled(boolean enabled) {
        this.askLlmEnabled.set(enabled);
    }

    /** Whether the agent may delegate tasks to sub-agents ({@code spawn_subagent}). */
    public boolean getSubagentsEnabled() {
        return subagentsEnabled.get();
    }

    public void setSubagentsEnabled(boolean enabled) {
        this.subagentsEnabled.set(enabled);
    }

    /** Global cap on tool-call rounds of a sub-agent (used when the role has no own budget). */
    public int getMaxSubagentTurns() {
        return maxSubagentTurns.get();
    }

    public void setMaxSubagentTurns(int turns) {
        this.maxSubagentTurns.set(turns);
    }

    /** Maximum nesting depth of sub-agent delegations (1 = children may not spawn children). */
    public int getMaxSubagentDepth() {
        return maxSubagentDepth.get();
    }

    public void setMaxSubagentDepth(int depth) {
        this.maxSubagentDepth.set(depth);
    }

    /**
     * Maximum number of sub-agents that run concurrently in one parallel {@code spawn_subagent}
     * call (the pool size; additional tasks queue and run as workers finish).
     */
    public int getMaxParallelSubagents() {
        return maxParallelSubagents.get();
    }

    public void setMaxParallelSubagents(int n) {
        this.maxParallelSubagents.set(n);
    }

    // --- context & history ---

    public boolean getAttachProofContext() {
        return attachProofContext.get();
    }

    public void setAttachProofContext(boolean v) {
        this.attachProofContext.set(v);
    }

    public int getProofContextMaxSequents() {
        return proofContextMaxSequents.get();
    }

    public void setProofContextMaxSequents(int v) {
        this.proofContextMaxSequents.set(v);
    }

    public int getProofContextMaxChars() {
        return proofContextMaxChars.get();
    }

    public void setProofContextMaxChars(int v) {
        this.proofContextMaxChars.set(v);
    }

    public int getMaxHistoryMessages() {
        return maxHistoryMessages.get();
    }

    public void setMaxHistoryMessages(int v) {
        this.maxHistoryMessages.set(v);
    }

    public int getMaxHistoryChars() {
        return maxHistoryChars.get();
    }

    public void setMaxHistoryChars(int v) {
        this.maxHistoryChars.set(v);
    }

    // --- files ---

    public int getMaxFileAttachments() {
        return maxFileAttachments.get();
    }

    public void setMaxFileAttachments(int v) {
        this.maxFileAttachments.set(v);
    }

    public int getMaxFileSizeKB() {
        return maxFileSizeKB.get();
    }

    public void setMaxFileSizeKB(int v) {
        this.maxFileSizeKB.set(v);
    }

    public int getMaxFileContentChars() {
        return maxFileContentChars.get();
    }

    public void setMaxFileContentChars(int v) {
        this.maxFileContentChars.set(v);
    }

    public int getMaxModelListingEntries() {
        return maxModelListingEntries.get();
    }

    public void setMaxModelListingEntries(int v) {
        this.maxModelListingEntries.set(v);
    }

    // --- tools & security ---

    public boolean getShellEnabled() {
        return shellEnabled.get();
    }

    public void setShellEnabled(boolean v) {
        this.shellEnabled.set(v);
    }

    public int getShellTimeoutSeconds() {
        return shellTimeoutSeconds.get();
    }

    public void setShellTimeoutSeconds(int v) {
        this.shellTimeoutSeconds.set(v);
    }

    public int getShellMaxOutputChars() {
        return shellMaxOutputChars.get();
    }

    public void setShellMaxOutputChars(int v) {
        this.shellMaxOutputChars.set(v);
    }

    public List<String> getShellBlockedPatterns() {
        return shellBlockedPatterns.get();
    }

    public void setShellBlockedPatterns(List<String> v) {
        this.shellBlockedPatterns.set(v);
    }

    public Set<String> getToolsDisabled() {
        return toolsDisabled.get();
    }

    public void setToolsDisabled(Set<String> v) {
        this.toolsDisabled.set(v);
    }

    public Set<String> getAllowedToolsWithApproval() {
        return allowedToolsWithApproval.get();
    }

    public void setAllowedToolsWithApproval(Set<String> val) {
        this.allowedToolsWithApproval.set(val);
    }

    public Set<String> getAllowedToolsWithoutApproval() {
        return allowedToolsWithoutApproval.get();
    }

    public void setAllowedToolsWithoutApproval(Set<String> val) {
        this.allowedToolsWithoutApproval.set(val);
    }

    /**
     * Tools that may run in the background although their metadata default says otherwise
     * (user override, see {@link #isBackgroundAllowed(String, boolean)}).
     */
    public Set<String> getBackgroundToolsEnabled() {
        return backgroundToolsEnabled.get();
    }

    public void setBackgroundToolsEnabled(Set<String> val) {
        this.backgroundToolsEnabled.set(val);
    }

    /**
     * Tools that must not run in the background although their metadata default allows it
     * (user override, see {@link #isBackgroundAllowed(String, boolean)}).
     */
    public Set<String> getBackgroundToolsDisabled() {
        return backgroundToolsDisabled.get();
    }

    public void setBackgroundToolsDisabled(Set<String> val) {
        this.backgroundToolsDisabled.set(val);
    }

    /** Maximum number of concurrently backgrounded tool calls (background jobs). */
    public int getMaxBackgroundJobs() {
        return maxBackgroundJobs.get();
    }

    public void setMaxBackgroundJobs(int n) {
        this.maxBackgroundJobs.set(Math.max(1, n));
    }

    /**
     * Effective background permission of a tool: the per-tool user overrides win, otherwise the
     * tool's metadata default applies.
     *
     * @param toolName the tool name
     * @param metadataDefault the tool's {@code backgroundable} metadata value
     */
    public boolean isBackgroundAllowed(String toolName, boolean metadataDefault) {
        if (backgroundToolsDisabled.get().contains(toolName)) {
            return false;
        }
        if (backgroundToolsEnabled.get().contains(toolName)) {
            return true;
        }
        return metadataDefault;
    }

    // --- prompt & skill libraries ---

    /** The raw (unexpanded) directories of the prompt library search path; empty = default. */
    public List<String> getPromptLibraryPaths() {
        return promptLibraryPaths.get();
    }

    public void setPromptLibraryPaths(List<String> v) {
        promptLibraryPaths.set(v);
    }

    /** The raw (unexpanded) directories of the skill library search path; empty = default. */
    public List<String> getSkillLibraryPaths() {
        return skillLibraryPaths.get();
    }

    public void setSkillLibraryPaths(List<String> v) {
        skillLibraryPaths.set(v);
    }

    // --- ui ---

    public boolean getAutoScrollOutput() {
        return autoScrollOutput.get();
    }

    public void setAutoScrollOutput(boolean v) {
        this.autoScrollOutput.set(v);
    }

    public boolean getShowToolActivity() {
        return showToolActivity.get();
    }

    public void setShowToolActivity(boolean v) {
        this.showToolActivity.set(v);
    }

    /** Merges the user-defined blocklist with the built-in defaults. */
    public List<String> getEffectiveShellBlockedPatterns() {
        var all = new ArrayList<>(DEFAULT_SHELL_BLOCKED_PATTERNS);
        for (String p : getShellBlockedPatterns()) {
            if (p != null && !p.isBlank() && !all.contains(p)) {
                all.add(p);
            }
        }
        return all;
    }

    /**
     * Returns the convenience accessor with the given key, or {@code null}.
     *
     * @param key one of the Turkish-style settings keys (unused placeholder for future use)
     */
    public @Nullable Object settingsBucket(String key) {
        return null;
    }
}
