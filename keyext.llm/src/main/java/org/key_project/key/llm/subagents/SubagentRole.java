/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.subagents;

import java.util.List;

import org.jspecify.annotations.Nullable;

/**
 * A named sub-agent role: the system prompt shown to the child model, a whitelist of tools it may
 * call, an optional model override and a per-role tool-round budget. Roles are contributed by
 * {@link SubagentRoleProvider}s (Java {@link java.util.ServiceLoader}) and listed in
 * {@link SubagentRegistry}; the {@code spawn_subagent} tool advertises them to the delegating
 * agent.
 *
 * @param name unique id used as the {@code role} argument of {@code spawn_subagent}
 * @param description short explanation shown to the delegating agent
 * @param systemPrompt instructions prepended to the child's system prompt
 * @param allowedTools whitelist of tool names the sub-agent may call; empty = inherit all enabled
 *        tools of the parent session
 * @param model optional model override ({@code null} = reuse the parent's model)
 * @param maxTurns per-child cap of tool-call rounds ({@code 0} = use the global
 *        {@code maxSubagentTurns} setting)
 * @param parallelAllowed whether {@code spawn_subagent} with {@code mode: parallel} is allowed
 *        for this role
 * @author Alexander Weigl
 */
public record SubagentRole(
        String name,
        String description,
        String systemPrompt,
        List<String> allowedTools,
        @Nullable String model,
        int maxTurns,
        boolean parallelAllowed) {

    public SubagentRole {
        name = name == null ? "" : name;
        description = description == null ? "" : description;
        systemPrompt = systemPrompt == null ? "" : systemPrompt;
        allowedTools = allowedTools == null ? List.of() : List.copyOf(allowedTools);
    }
}
