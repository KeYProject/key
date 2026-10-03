/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm.mcp;

import java.util.List;

/**
 * Provides the built-in KeY-Agent tool set (proof context, file access, shell, questions) to the
 * {@link BuiltInMCPClient}. Registered via {@code META-INF/services} (replacing the former echo and
 * calculate demo tools).
 *
 * @author Alexander Weigl
 */
public final class KeYAgentToolsProvider implements McpToolProvider {
    private final KeYAgentTools agentTools = new KeYAgentTools();

    @Override
    public List<McpClient> get() {
        return List.of(agentTools);
    }
}
