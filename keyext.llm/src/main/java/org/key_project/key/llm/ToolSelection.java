/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.jspecify.annotations.Nullable;

/**
 * Decides which tools are advertised to the model in one request.
 * <p>
 * The tool set is split into two tiers:
 * <ul>
 * <li><b>Standard tools</b> (every category except {@link ToolCategory#PROOF} and
 * {@link ToolCategory#TACLETS}) are always advertised, restricted by the active skill's
 * {@code allowedTools} whitelist (empty whitelist = no restriction).</li>
 * <li><b>KeY-specific tools</b> ({@link ToolCategory#isKeySpecific()}, i.e. Proof and Taclets)
 * are only advertised once the agent loaded them via the {@code list_tools} discovery tool; the
 * {@code keySpecificLoaded} set carries those names into the request.</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class ToolSelection {

    private ToolSelection() {
    }

    /**
     * The OpenAI-format tool definitions advertised in one request: the always-on standard tools
     * plus the requested KeY-specific tools, both filtered by the active skill's whitelist.
     *
     * @param session the session whose tool registry is queried
     * @param skill the active skill ({@code null} or an empty {@code allowedTools} list disables
     *        the whitelist filter)
     * @param keySpecificLoaded the KeY-specific tool names the agent loaded via {@code list_tools}
     */
    public static List<Map<String, Object>> advertisedTools(LlmSession session,
            @Nullable Skill skill, Set<String> keySpecificLoaded) {
        return session.getMcpClient().getTools().stream()
                .filter(t -> !t.category().isKeySpecific()
                        || keySpecificLoaded.contains(t.function().name()))
                .filter(t -> skill == null || skill.allowedTools().isEmpty()
                        || skill.allowedTools().contains(t.function().name()))
                .map(Tool::toMap)
                .toList();
    }
}
