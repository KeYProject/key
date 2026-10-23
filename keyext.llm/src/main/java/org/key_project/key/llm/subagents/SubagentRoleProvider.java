/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.subagents;

import java.util.List;

/**
 * Service provider for sub-agent roles. Implementations are discovered through the Java
 * {@link java.util.ServiceLoader} (service file
 * {@code META-INF/services/org.key_project.key.llm.subagents.SubagentRoleProvider}) and their
 * roles are aggregated by {@link SubagentRegistry} - the same pattern as the modular tool set
 * ({@code AgentToolProvider}), so plugins can add their own roles.
 *
 * @author Alexander Weigl
 */
public interface SubagentRoleProvider {

    /** The roles contributed by this provider. */
    List<SubagentRole> get();
}
