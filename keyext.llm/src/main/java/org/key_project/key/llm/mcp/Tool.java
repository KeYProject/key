/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm.mcp;

import java.util.Map;

/**
 * A tool definition in the OpenAI tool format plus KeY-side metadata.
 *
 * @param type the tool type, always {@code "function"}
 * @param function the function definition
 * @param defaultApproval whether this tool is safe to run without asking the user by default
 */
public record Tool(String type, FunctionDefinition function,
        ApprovalRequirement defaultApproval) {

    public Tool(FunctionDefinition function) {
        this("function", function, ApprovalRequirement.AUTO);
    }

    public Tool(FunctionDefinition function, ApprovalRequirement defaultApproval) {
        this("function", function, defaultApproval);
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
