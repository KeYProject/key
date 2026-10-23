/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayDeque;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CopyOnWriteArrayList;

import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests sub-agent delegation through {@code spawn_subagent}: the nested loop executes the child's
 * tool calls and returns its final answer, the role whitelist blocks foreign tools, the settings
 * gate and the depth guard stop unwanted delegations, and parallel mode is only accepted for
 * roles that allow it (and is reported as not implemented yet).
 */
class SubagentLoopTest {

    private LlmSession session;

    @BeforeEach
    void setUp() {
        LlmSettings.INSTANCE.setMaxToolRounds(8);
        LlmSettings.INSTANCE.setMaxSubagentTurns(4);
        LlmSettings.INSTANCE.setMaxSubagentDepth(2);
        LlmSettings.INSTANCE.setSubagentsEnabled(false);
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setToolsDisabled(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setAgentCanUseSkills(false);
        TestMcpToolProvider.reset();
        session = new LlmSession("https://example.invalid", "token", "model");
    }

    @Test
    void spawnRunsChildLoopAndReturnsItsAnswer() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"echo-role\",\"task\":\"say hi\",\"mode\":\"sequential\"}")),
            ""));
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{\"x\":1}")), ""));
        mock.thenRespond(MockCompletions.text("KEY_AGENT_RESULT {\"summary\":\"hi\"}\ndone"));
        mock.thenRespond(MockCompletions.text("sub-agent says: done"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var done = (AgentResult.Done) result;
        assertTrue(done.content().contains("sub-agent says: done"),
            "expected the parent's continuation, got: " + done.content());

        // the child executed its tool call through the session client
        assertEquals(List.of("echo_test|{\"x\":1}"), TestMcpToolProvider.EXECUTED);

        // four requests: parent #1, child #1, child #2 (final), parent #2 (final)
        assertEquals(4, mock.sent.size());
        var childRequest = mock.sent.get(1);
        assertEquals("system", childRequest.messages().get(0).get("role"));
        assertTrue(String.valueOf(childRequest.messages().get(0).get("content")).contains(
            "echo-role"),
            "child system prompt must carry the role name");
        assertEquals("say hi", childRequest.messages().get(1).get("content"));
        // only the whitelisted test tool is advertised to the child
        assertEquals(1, childRequest.tools().size());
        assertTrue(String.valueOf(childRequest.tools().get(0)).contains("echo_test"));
    }

    @Test
    void roleWhitelistBlocksForeignTools() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"echo-role\",\"task\":\"x\"}")),
            ""));
        // the (misbehaving) child tries a tool outside its whitelist
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.NEEDS_APPROVAL, "{}")), ""));
        mock.thenRespond(MockCompletions.text("done"));
        mock.thenRespond(MockCompletions.text("parent done"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertFalse(TestMcpToolProvider.EXECUTED.stream()
                .anyMatch(e -> e.startsWith(TestMcpToolProvider.NEEDS_APPROVAL)),
            "foreign tool must never be executed");
        // the blocked call is reported back into the child's thread
        var followUp = mock.sent.get(2).messages();
        var last = followUp.get(followUp.size() - 1);
        assertEquals("tool", last.get("role"));
        assertTrue(String.valueOf(last.get("content")).contains("not in the whitelist"));
    }

    @Test
    void disabledBySettingsFlag() {
        // subagentsEnabled is false from setUp
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"echo-role\",\"task\":\"x\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("understood"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty(), "no child may run while disabled");
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertEquals("s1", toolMsg.get("tool_call_id"));
        assertTrue(String.valueOf(toolMsg.get("content")).contains("disabled"));
    }

    @Test
    void unknownRoleIsReported() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"no-such-role\",\"task\":\"x\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("fine"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty());
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("unknown role"));
    }

    @Test
    void depthGuardStopsNestedSpawns() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        LlmSettings.INSTANCE.setMaxSubagentDepth(1); // children may not spawn children
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"spawner-role\",\"task\":\"delegate deep\"}")),
            ""));
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s2", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"spawner-role\",\"task\":\"deeper\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("done"));
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertEquals(4, mock.sent.size());
        // the child's follow-up request contains the blocked grandchild as a tool result
        var followUp = mock.sent.get(2).messages();
        var last = followUp.get(followUp.size() - 1);
        assertEquals("tool", last.get("role"));
        assertTrue(String.valueOf(last.get("content")).contains("maximum nesting depth"));
    }

    @Test
    void parallelModeIsCheckedButNotImplemented() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        // echo-role allows parallel but parallel is not implemented yet
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"echo-role\",\"task\":\"x\",\"mode\":\"parallel\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty(), "parallel children must not run");
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("not implemented yet"));
    }

    @Test
    void parallelModeRejectedForSequentialOnlyRoles() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        // the built-in rule-designer is flagged sequential-only
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"rule-designer\",\"task\":\"x\",\"mode\":\"parallel\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("does not allow parallel"));
    }

    /** Scripted {@link ChatCompletionsClient}, shared with the parent and the child loop. */
    static class MockCompletions implements ChatCompletionsClient {
        private final ArrayDeque<Map<String, Object>> script = new ArrayDeque<>();
        final List<AgentRequest> sent = new CopyOnWriteArrayList<>();

        void thenRespond(Map<String, Object> response) {
            script.add(response);
        }

        @Override
        public Map<String, Object> complete(LlmSession session, AgentRequest request) {
            sent.add(request);
            if (script.isEmpty()) {
                throw new IllegalStateException("no scripted response left");
            }
            return script.removeFirst();
        }

        static Map<String, Object> text(String content) {
            return Map.of("choices", List.of(Map.of("message",
                Map.of("role", "assistant", "content", content))));
        }

        static Map<String, Object> toolCalls(List<Map<String, Object>> calls, String content) {
            return Map.of("choices", List.of(Map.of("message",
                Map.of("role", "assistant", "content", content, "tool_calls", calls))));
        }

        static Map<String, Object> tool(String id, String name, String arguments) {
            return Map.of("id", id, "type", "function",
                "function", Map.of("name", name, "arguments", arguments));
        }
    }
}
