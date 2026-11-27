/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.Map;

import org.jspecify.annotations.Nullable;

/**
 * One request towards the chat-completion API, assembled by {@link ExtendedPrompt}.
 * <p>
 * The messages are already fully resolved (system prompt, history, context blocks, file
 * attachments, user prompt). The {@code tools} list contains the OpenAI-format tool definitions
 * for the active tool set.
 *
 * @param model the model id to use
 * @param messages the message list in wire format
 * @param tools the tool definitions in wire format (may be empty)
 * @param temperature optional temperature override ({@code null} = use model default)
 * @param maxOutputTokens optional cap on generated tokens ({@code null} = no cap)
 * @param maxToolRounds maximum number of tool-call rounds within one agent turn
 */
public record AgentRequest(
        String model,
        List<Map<String, Object>> messages,
        List<Map<String, Object>> tools,
        @Nullable Double temperature,
        @Nullable Integer maxOutputTokens,
        int maxToolRounds) {

    public AgentRequest {
        tools = tools == null ? List.of() : List.copyOf(tools);
        messages = List.copyOf(messages);
    }

    /** Creates a request with model defaults for temperature and output tokens. */
    public static AgentRequest of(String model, List<Map<String, Object>> messages,
            List<Map<String, Object>> tools, int maxToolRounds) {
        return new AgentRequest(model, messages, tools, null, null, maxToolRounds);
    }
}
