/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

/**
 * The category of a tool: pure KeY-side metadata used to group and sort the tool set in the tool
 * documentation and in the settings UI. It is never sent to the model (the OpenAI tool format
 * only knows name/description/parameters).
 * <p>
 * The enum declaration order is the grouping/sort order: {@link #PROOF} first, then
 * {@link #FILES}, {@link #SHELL}, {@link #TACLETS}, {@link #INTERACTION},
 * {@link #SUBAGENTS}, {@link #DOCUMENTATION} and finally {@link #GENERAL} (the default for
 * tools contributed by external MCP clients that carry no category).
 *
 * @author Alexander Weigl
 */
public enum ToolCategory {
    PROOF("Proof"),
    FILES("Files"),
    SHELL("Shell"),
    TACLETS("Taclets"),
    INTERACTION("Interaction"),
    SUBAGENTS("Sub-agents"),
    DOCUMENTATION("Documentation"),
    GENERAL("General");

    private final String label;

    ToolCategory(String label) {
        this.label = label;
    }

    /** The human-readable category name, used in headings and badges. */
    public String label() {
        return label;
    }

    @Override
    public String toString() {
        return label;
    }
}
