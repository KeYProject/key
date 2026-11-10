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
 * <p>
 * Categories come in two tiers: the KeY-specific tools {@link #PROOF} and {@link #TACLETS}
 * (see {@link #isKeySpecific()}) are only offered to the model on request (via the
 * {@code list_tools} discovery tool) and are the tools exposed on the KeY MCP server. All other
 * categories are <em>standard</em> tools: they are always advertised to the chat agent (subject
 * to the active skill's whitelist) and never exposed over MCP.
 *
 * @author Alexander Weigl
 */
public enum ToolCategory {
    PROOF("Proof", true),
    FILES("Files", false),
    SHELL("Shell", false),
    TACLETS("Taclets", true),
    INTERACTION("Interaction", false),
    SUBAGENTS("Sub-agents", false),
    DOCUMENTATION("Documentation", false),
    GENERAL("General", false);

    private final String label;
    private final boolean keySpecific;

    ToolCategory(String label, boolean keySpecific) {
        this.label = label;
        this.keySpecific = keySpecific;
    }

    /** The human-readable category name, used in headings and badges. */
    public String label() {
        return label;
    }

    /**
     * Whether this category holds KeY-specific tools ({@link #PROOF}, {@link #TACLETS}): such
     * tools are loaded on request through the {@code list_tools} discovery tool instead of being
     * advertised by default, and they are the only tools exposed on the KeY MCP server.
     */
    public boolean isKeySpecific() {
        return keySpecific;
    }

    @Override
    public String toString() {
        return label;
    }
}
