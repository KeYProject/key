/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayDeque;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicInteger;

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
 * gate and the depth guard stop unwanted delegations, and parallel mode fans out over a tasks
 * array (only for roles that allow it, with a thread-safe client expectation).
 */
class SubagentLoopTest {

    private LlmSession session;

    @BeforeEach
    void setUp() {
        LlmSettings.INSTANCE.setMaxToolRounds(8);
        LlmSettings.INSTANCE.setMaxSubagentTurns(4);
        LlmSettings.INSTANCE.setMaxSubagentDepth(2);
        LlmSettings.INSTANCE.setMaxParallelSubagents(4);
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
    void parallelRunExecutesAllTasksAndMergesResults() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new ParallelMock();
        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate parallel", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var done = (AgentResult.Done) result;
        assertTrue(done.content().contains("all done"),
            "expected the parent's continuation, got: " + done.content());

        // both workers ran; task A also executed a tool call
        assertTrue(mock.sent.stream().anyMatch(r -> hasUser(r, "B1")),
            "worker for task B1 must have run");
        assertEquals(List.of("echo_test|{\"x\":\"A\"}"), TestMcpToolProvider.EXECUTED);

        // the parent's final request carries the merged parallel report
        var finalReq = mock.sent.get(mock.sent.size() - 1);
        var toolMsg = (Map<String, Object>) finalReq.messages().get(
            finalReq.messages().size() - 1);
        var content = String.valueOf(toolMsg.get("content"));
        assertTrue(content.contains("[parallel run of 2 sub-agents"),
            "expected the parallel report, got: " + content);
        assertTrue(content.contains("(1)") && content.contains("(2)"), content);
        assertTrue(content.contains("A resolved"), content);
        assertTrue(content.contains("B resolved"), content);
    }

    @Test
    void parallelRequiresTasksArray() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        // mode parallel but only a single 'task', no 'tasks' array
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"echo-role\",\"task\":\"x\",\"mode\":\"parallel\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty());
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("tasks"),
            "parallel mode without a tasks array must be rejected");
    }

    @Test
    void parallelNestedSpawnIsDepthGuarded() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        LlmSettings.INSTANCE.setMaxSubagentDepth(1); // children may not spawn children
        var mock = new ParallelMock(true); // parent spawns a parallel-spawner with a 'nest' task
        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate parallel", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);

        // a parallel worker (depth 1) that tries to spawn again is blocked at the depth guard
        var workerFollowUp = mock.sent.stream()
                .filter(r -> hasUser(r, "nest"))
                .map(r -> (Map<String, Object>) r.messages().get(r.messages().size() - 1))
                .filter(m -> "tool".equals(m.get("role")))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no worker tool result found"));
        assertTrue(String.valueOf(workerFollowUp.get("content")).contains("maximum nesting depth"));
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

    @Test
    void sequentialSpawnRecordsSubagentRunAndActivity() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"echo-role\",\"task\":\"say hi\",\"mode\":\"sequential\"}")),
            ""));
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{\"x\":1}")), ""));
        mock.thenRespond(MockCompletions.text("KEY_AGENT_RESULT {\"summary\":\"hi\"}\ndone"));
        mock.thenRespond(MockCompletions.text("parent done"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);

        // the run is recorded on the session's log
        assertEquals(1, session.getSubagentLog().size());
        var run = session.getSubagentLog().snapshot(1).get(0);
        assertEquals("echo-role", run.role());
        assertEquals("sequential", run.mode());
        assertEquals(1, run.tasks().size());
        var task = run.tasks().get(0);
        assertEquals("say hi", task.task());
        assertEquals(SubagentLog.Status.OK, task.status());
        assertEquals(1, task.rounds());
        assertEquals(List.of("echo_test"), task.tools());
        assertTrue(task.outcome().contains("finished after 1 tool round"));

        // the spawn tool activity carries one indented child per task
        var done = (AgentResult.Done) result;
        assertEquals(1, done.activities().size());
        var children = done.activities().get(0).children();
        assertEquals(1, children.size());
        assertEquals("echo-role", children.get(0).name());
        assertEquals("say hi", children.get(0).arguments());
        assertTrue(children.get(0).result().contains("sequential"),
            "expected mode in the child activity result, got: " + children.get(0).result());
    }

    @Test
    void parallelSpawnRecordsParallelRunWithPerTaskResults() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new ParallelMock();
        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate parallel", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertEquals(1, session.getSubagentLog().size());
        var run = session.getSubagentLog().snapshot(1).get(0);
        assertEquals("echo-role", run.role());
        assertEquals("parallel", run.mode());
        assertEquals(2, run.tasks().size());
        assertTrue(run.tasks().stream().allMatch(t -> t.status() == SubagentLog.Status.OK));
        assertTrue(run.tasks().stream().anyMatch(t -> t.tools().contains("echo_test")),
            "task A must have called the echo tool");

        var done = (AgentResult.Done) result;
        assertEquals(2, done.activities().get(0).children().size());
    }

    @Test
    void subagentStoppedAtRoundLimitIsRecorded() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"echo-role\",\"task\":\"loop\",\"mode\":\"sequential\"}")),
            ""));
        for (int i = 1; i <= 4; i++) { // echo-role's budget is 4 tool rounds
            mock.thenRespond(MockCompletions.toolCalls(
                List.of(MockCompletions.tool("c" + i, TestMcpToolProvider.ECHO, "{\"x\":1}")), ""));
        }
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var task = session.getSubagentLog().snapshot(1).get(0).tasks().get(0);
        assertEquals(SubagentLog.Status.STOPPED, task.status());
        assertEquals(4, task.rounds());
        assertEquals(4, task.tools().size());
        assertTrue(task.outcome().contains("reached its tool-round limit"));
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

    private static boolean hasUser(AgentRequest request, String content) {
        return request.messages().stream()
                .filter(m -> "user".equals(m.get("role")))
                .map(m -> String.valueOf(m.get("content")))
                .anyMatch(content::equals);
    }

    /**
     * Thread-safe mock for parallel fan-out: the response for each request is derived from its
     * user message, so worker threads can interleave arbitrarily and every request still gets a
     * deterministic response. The parent's messages drive the outer script.
     */
    static class ParallelMock implements ChatCompletionsClient {
        /** Every request, in arrival order (thread-safe). */
        final List<AgentRequest> sent = new CopyOnWriteArrayList<>();
        private final Map<String, Integer> perTask = new ConcurrentHashMap<>();
        private final AtomicInteger parentCalls = new AtomicInteger();
        private final boolean spawnNesting;

        ParallelMock() {
            this(false);
        }

        ParallelMock(boolean spawnNesting) {
            this.spawnNesting = spawnNesting;
        }

        @Override
        public Map<String, Object> complete(LlmSession session, AgentRequest request) {
            sent.add(request);
            String user = request.messages().stream()
                    .filter(m -> "user".equals(m.get("role")))
                    .map(m -> String.valueOf(m.get("content")))
                    .findFirst().orElse("");
            if (user.equals("delegate parallel")) {
                if (parentCalls.incrementAndGet() != 1) {
                    return MockCompletions.text("all done");
                }
                return spawnNesting
                        ? MockCompletions.toolCalls(List.of(MockCompletions.tool("s1",
                            KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                            "{\"role\":\"parallel-spawner-role\",\"tasks\":[\"nest\"],"
                                + "\"mode\":\"parallel\"}")),
                            "")
                        : MockCompletions.toolCalls(List.of(MockCompletions.tool("s1",
                            KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                            "{\"role\":\"echo-role\",\"tasks\":[\"A1\",\"B1\"],\"mode\":\"parallel\"}")),
                            "");
            }
            if (user.startsWith("A")) {
                return perTask.merge("A", 1, Integer::sum) == 1
                        ? MockCompletions.toolCalls(List.of(MockCompletions.tool("a1",
                            TestMcpToolProvider.ECHO, "{\"x\":\"A\"}")), "")
                        : MockCompletions.text("A resolved");
            }
            if (user.startsWith("B")) {
                return MockCompletions.text("B resolved");
            }
            if (user.startsWith("nest")) {
                return perTask.merge("nest", 1, Integer::sum) == 1
                        ? MockCompletions.toolCalls(List.of(MockCompletions.tool("n1",
                            KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                            "{\"role\":\"spawner-role\",\"task\":\"deeper\"}")), "")
                        : MockCompletions.text("nest done");
            }
            return MockCompletions.text("all done");
        }
    }
}
