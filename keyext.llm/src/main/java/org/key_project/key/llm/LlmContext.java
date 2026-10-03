/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Conversation context maintained per proof (see {@link LlmSession}).
 * <p>
 * Unlike the original implementation, messages may carry additional protocol fields:
 * {@code tool_call_id} for tool results and {@code tool_calls} for assistant messages that
 * requested tool executions. This is required to continue a tool-calling conversation with
 * OpenAI-compatible endpoints.
 *
 * @author Alexander Weigl
 */
public class LlmContext {
    private final List<LlmMessage> messages = new ArrayList<>();

    public void addMessage(LlmMessage message) {
        messages.add(message);
    }

    public void addMessages(Collection<LlmMessage> msgs) {
        messages.addAll(msgs);
    }

    public void clear() {
        messages.clear();
    }

    public boolean isEmpty() {
        return messages.isEmpty();
    }

    public List<LlmMessage> getMessages() {
        return messages;
    }

    /**
     * A single chat message in OpenAI-style wire terms.
     *
     * @param role "system", "user", "assistant" or "tool"
     * @param content text content (empty string for pure tool-call assistant messages)
     * @param toolCallId the {@code tool_call_id} for role "tool"
     * @param toolCalls the tool calls for role "assistant"
     */
    public record LlmMessage(String role, String content, String toolCallId,
            List<Map<String, Object>> toolCalls) {

        public LlmMessage {
            content = content == null ? "" : content;
        }

        public LlmMessage(String role, String content) {
            this(role, content, null, null);
        }

        public static LlmMessage user(String content) {
            return new LlmMessage("user", content);
        }

        public static LlmMessage assistant(String content) {
            return new LlmMessage("assistant", content);
        }

        public static LlmMessage assistant(String content, List<Map<String, Object>> toolCalls) {
            return new LlmMessage("assistant", content, null, toolCalls);
        }

        public static LlmMessage tool(String toolCallId, String content) {
            return new LlmMessage("tool", content, toolCallId, null);
        }

        public static LlmMessage system(String content) {
            return new LlmMessage("system", content);
        }

        /** Serializes this message to the OpenAI wire format. */
        public Map<String, Object> toOpenAiMap() {
            var m = new LinkedHashMap<String, Object>();
            m.put("role", role);
            m.put("content", content);
            if (toolCallId != null) {
                m.put("tool_call_id", toolCallId);
            }
            if (toolCalls != null) {
                m.put("tool_calls", toolCalls);
            }
            return m;
        }
    }
}
