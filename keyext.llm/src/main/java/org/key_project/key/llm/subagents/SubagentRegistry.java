/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.subagents;

import java.util.List;
import java.util.ServiceLoader;
import java.util.TreeMap;

import org.jspecify.annotations.Nullable;

/**
 * Registry of all sub-agent roles contributed by {@link SubagentRoleProvider}s, sorted by name.
 * Used by the {@code spawn_subagent} tool (whose schema advertises the role names) and by
 * {@code SubagentRunner} (which resolves the role for a delegation).
 *
 * @author Alexander Weigl
 */
public final class SubagentRegistry {

    public static final SubagentRegistry INSTANCE = new SubagentRegistry();

    private final TreeMap<String, SubagentRole> roles = new TreeMap<>();

    private SubagentRegistry() {
        for (var provider : ServiceLoader.load(SubagentRoleProvider.class)) {
            for (var role : provider.get()) {
                if (role != null && role.name() != null && !role.name().isBlank()) {
                    roles.putIfAbsent(role.name(), role);
                }
            }
        }
    }

    /** All registered roles, sorted by name. */
    public List<SubagentRole> all() {
        return List.copyOf(roles.values());
    }

    /** The role with the given name, or {@code null}. */
    public @Nullable SubagentRole get(String name) {
        return name == null ? null : roles.get(name);
    }

    /** Names of all registered roles (for the tool schema and error messages), sorted. */
    public List<String> roleNames() {
        return List.copyOf(roles.keySet());
    }
}
