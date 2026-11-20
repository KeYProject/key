/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;

/**
 * A user-defined skill: named instructions that are appended to the system prompt while the skill
 * is active, plus an optional restriction of the tool set.
 *
 * @param name unique id (also the file name)
 * @param description shown in menus/autocompletion and to the agent
 * @param instructions extra system-level context appended while the skill is active
 * @param allowedTools optional whitelist of tool names (empty = no restriction)
 * @param enabled whether the skill can be selected/used
 */
public record Skill(String name, String description, String instructions,
        List<String> allowedTools, boolean enabled) {

    public Skill {
        name = name == null ? "" : name;
        description = description == null ? "" : description;
        instructions = instructions == null ? "" : instructions;
        allowedTools = allowedTools == null ? List.of() : List.copyOf(allowedTools);
    }
}
