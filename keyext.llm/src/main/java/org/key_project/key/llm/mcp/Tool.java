/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.util.Map;

/**
 * A tool definition in the OpenAI tool format plus KeY-side metadata.
 *
 * @param type the tool type, always {@code "function"}
 * @param function the function definition
 * @param defaultApproval whether this tool is safe to run without asking the user by default
 * @param category the KeY-side tool category (grouping/sorting metadata; default
 *        {@link ToolCategory#GENERAL})
 * @param backgroundable whether this tool may run in the background (user can detach a running
 *        call; its result is delivered to the agent when it finishes)
 */
public record Tool(String type, FunctionDefinition function,
        ApprovalRequirement defaultApproval, ToolCategory category, boolean backgroundable) {

    public Tool(FunctionDefinition function) {
        this("function", function, ApprovalRequirement.AUTO, ToolCategory.GENERAL, false);
    }

    public Tool(FunctionDefinition function, ApprovalRequirement defaultApproval) {
        this("function", function, defaultApproval, ToolCategory.GENERAL, false);
    }

    public Tool(FunctionDefinition function, ApprovalRequirement defaultApproval,
            ToolCategory category, boolean backgroundable) {
        this("function", function, defaultApproval, category, backgroundable);
    }

    /** Converts this tool to the OpenAI-format map (approval metadata is not serialized). */
    public Map<String, Object> toMap() {
        return Map.of("type", type, "function", function.toMap());
    }

    public enum ApprovalRequirement {
        /** Run without asking the user (unless the user configured approval explicitly). */
        AUTO,
        /** Ask the user before the first execution in a turn, by default. */
        ASK
    }
}
