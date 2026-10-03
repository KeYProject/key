/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm.mcp;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.ServiceLoader;
import java.util.Set;
import java.util.TreeSet;

import org.key_project.key.llm.LlmSettings;

import org.jspecify.annotations.Nullable;

/**
 * Registry facade over all registered {@link McpClient} instances.
 * <p>
 * <b>Approval model:</b> approved tools are advertised; whether an invocation requires user
 * approval is decided dynamically by {@link #requiresApproval(String)}:
 * <ol>
 * <li>tools in {@code allowedToolsWithoutApproval} never prompt (read-only defaults),</li>
 * <li>tools in {@code allowedToolsWithApproval} always prompt,</li>
 * <li>otherwise the tool's own default applies ({@link Tool.ApprovalRequirement}).</li>
 * </ol>
 * The sets are read live from {@link LlmSettings} so that session-scoped clients always see the
 * current configuration. Disabled tools are not advertised and cannot be invoked.
 *
 * @author Alexander Weigl
 */
public class BuiltInMCPClient implements McpClient {
    private final Map<String, McpClient> toolOwners = new HashMap<>();
    private boolean isClosed = false;

    public BuiltInMCPClient() {
        var loader = ServiceLoader.load(McpToolProvider.class);
        for (var provider : loader.stream().map(it -> it.get()).toList()) {
            for (var client : provider.get()) {
                register(client);
            }
        }
    }

    private void register(McpClient client) {
        for (Tool tool : client.getTools()) {
            toolOwners.putIfAbsent(tool.function().name(), client);
        }
    }

    /** Names of all known tools (including disabled ones; used by the settings UI). */
    public Set<String> getAllToolNames() {
        return new TreeSet<>(toolOwners.keySet());
    }

    /**
     * Returns the enabled tool definitions in OpenAI format, i.e. all registered tools except those
     * listed in {@code toolsDisabled}. Never mutates the approval sets.
     */
    @Override
    public synchronized List<Tool> getTools() {
        var disabled = LlmSettings.INSTANCE.getToolsDisabled();
        return toolOwners.keySet().stream().sorted()
                .filter(name -> !disabled.contains(name))
                .map(toolOwners::get).distinct()
                .flatMap(client -> client.getTools().stream())
                .filter(tool -> !disabled.contains(tool.function().name()))
                .toList();
    }

    /** Whether calling the given tool requires user approval (never throws for unknown tools). */
    public boolean requiresApproval(String toolName) {
        var settings = LlmSettings.INSTANCE;
        if (settings.getAllowedToolsWithoutApproval().contains(toolName)) {
            return false;
        }
        if (settings.getAllowedToolsWithApproval().contains(toolName)) {
            return true;
        }
        Tool tool = findTool(toolName);
        return tool == null || tool.defaultApproval() == Tool.ApprovalRequirement.ASK;
    }

    /** Whether the tool is currently disabled in the settings. */
    public boolean isDisabled(String toolName) {
        return LlmSettings.INSTANCE.getToolsDisabled().contains(toolName);
    }

    /** Remembers the tool as approved without further prompts ("always allow this tool"). */
    public void allowWithoutApproval(String toolName) {
        var allowed = new TreeSet<>(LlmSettings.INSTANCE.getAllowedToolsWithoutApproval());
        allowed.add(toolName);
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(allowed);
        var with = new TreeSet<>(LlmSettings.INSTANCE.getAllowedToolsWithApproval());
        with.remove(toolName);
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(with);
    }

    /** Removes the tool from both approval sets (back to its default behavior). */
    public void resetApproval(String toolName) {
        var with = new TreeSet<>(LlmSettings.INSTANCE.getAllowedToolsWithApproval());
        var without = new TreeSet<>(LlmSettings.INSTANCE.getAllowedToolsWithoutApproval());
        with.remove(toolName);
        without.remove(toolName);
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(with);
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(without);
    }

    /**
     * Invokes the tool on the owning client, after a disabled check. The invoked client itself
     * applies additional safety measures (e.g. the shell blocklist).
     */
    @Override
    public Object callTool(String toolName, String arguments) throws Exception {
        if (isDisabled(toolName)) {
            throw new McpToolNowAllowedException();
        }
        var owner = toolOwners.get(toolName);
        if (owner == null) {
            throw new IllegalArgumentException("unknown tool: " + toolName);
        }
        return owner.callTool(toolName, arguments);
    }

    private @Nullable Tool findTool(String toolName) {
        var owner = toolOwners.get(toolName);
        if (owner == null) {
            return null;
        }
        return owner.getTools().stream().filter(t -> toolName.equals(t.function().name()))
                .findFirst().orElse(null);
    }

    public List<Tool> toolsOf(String toolName) {
        var owner = toolOwners.get(toolName);
        return owner == null ? List.of() : owner.getTools();
    }

    @Override
    public boolean isClosed() {
        return isClosed;
    }

    @Override
    public void close() {
        isClosed = true;
    }
}
