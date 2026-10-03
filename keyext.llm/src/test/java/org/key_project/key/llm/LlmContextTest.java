/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.util.List;
import java.util.Map;

import org.key_project.key.llm.LlmContext.LlmMessage;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the OpenAI wire serialization of {@link LlmMessage}.
 */
class LlmContextTest {

    @Test
    void plainUserMessageHasMinimalFields() {
        var map = LlmMessage.user("hello").toOpenAiMap();
        assertEquals("user", map.get("role"));
        assertEquals("hello", map.get("content"));
        assertFalse(map.containsKey("tool_call_id"));
        assertFalse(map.containsKey("tool_calls"));
    }

    @Test
    void toolResultCarriesToolCallId() {
        var map = LlmMessage.tool("call_42", "result text").toOpenAiMap();
        assertEquals("tool", map.get("role"));
        assertEquals("call_42", map.get("tool_call_id"));
        assertEquals("result text", map.get("content"));
    }

    @Test
    void assistantToolCallsAreSerialized() {
        var calls = List.<Map<String, Object>>of(Map.of("id", "c1", "type", "function"));
        var map = LlmMessage.assistant("", calls).toOpenAiMap();
        assertEquals("assistant", map.get("role"));
        assertEquals(calls, map.get("tool_calls"));
        assertFalse(map.containsKey("tool_call_id"));
    }

    @Test
    void nullContentBecomesEmptyString() {
        var map = new LlmMessage("user", null).toOpenAiMap();
        assertEquals("", map.get("content"));
    }

    @Test
    void contextAppendsAndClears() {
        var ctx = new LlmContext();
        assertTrue(ctx.isEmpty());
        ctx.addMessage(LlmMessage.user("a"));
        ctx.addMessage(LlmMessage.assistant("b"));
        assertEquals(2, ctx.getMessages().size());
        assertNull(ctx.getMessages().get(0).toolCallId());
        ctx.clear();
        assertTrue(ctx.isEmpty());
    }
}
