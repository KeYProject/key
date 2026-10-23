/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.util.List;

/**
 * Contributes one or several {@link AgentTool}s to the KeY-Agent tool set. Providers are
 * discovered via the Java {@link java.util.ServiceLoader} and registered under
 * {@code META-INF/services/org.key_project.key.llm.mcp.AgentToolProvider}; {@link KeYAgentTools}
 * aggregates every provider it finds at construction time.
 * <p>
 * Plugins (or test suites) that want to extend the agent's capabilities simply implement this
 * interface, hand out their tools from {@link #get()} and add a service file entry.
 *
 * @author Alexander Weigl
 */
public interface AgentToolProvider {
    /**
     * Returns the tools contributed by this provider. A tool name must be unique across all
     * providers; the first registered tool of a name wins.
     *
     * @return the tools of this provider (may be empty)
     */
    List<AgentTool> get();
}
