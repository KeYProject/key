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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the {@link AgentLoop}: bounded tool rounds, correct follow-up messages (no prompt
 * duplication), question pause/resume and approval pause/resume.
 */
class AgentLoopTest {

    private LlmSession session;

    @BeforeEach
    void setUp() {
        LlmSettings.INSTANCE.setMaxToolRounds(8);
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setToolsDisabled(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setAgentCanUseSkills(false);
        TestMcpToolProvider.reset();
        session = new LlmSession("https://example.invalid", "token", "model");
    }

    @Test
    void toolRoundLimitIsEnforced() {
        var mock = new MockCompletions();
        // the model keeps calling a tool forever
        for (int i = 0; i < 100; i++) {
            mock.thenRespond(MockCompletions.toolCalls(
                List.of(MockCompletions.tool("call" + i, TestMcpToolProvider.ECHO, "{\"x\":1}")),
                ""));
        }
        LlmSettings.INSTANCE.setMaxToolRounds(2);

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("hello", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var done = (AgentResult.Done) result;
        assertTrue(done.content().contains("tool rounds"),
            "expected a tool-limit note, got: " + done.content());
        // two rounds were executed and both tool results went into the context
        long assistantToolMessages = session.getContext().getMessages().stream()
                .filter(m -> "assistant".equals(m.role()) && m.toolCalls() != null).count();
        long toolMessages =
            session.getContext().getMessages().stream().filter(m -> "tool".equals(m.role()))
                    .count();
        assertEquals(2, assistantToolMessages);
        assertEquals(2, toolMessages);
    }

    @Test
    void followUpRequestsDoNotDuplicateTheUserPrompt() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{\"x\":1}")), ""));
        mock.thenRespond(MockCompletions.text("final answer"));
        mock.thenRespond(MockCompletions.text("unused"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("my prompt", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertEquals("final answer", ((AgentResult.Done) result).content());
        assertEquals(2, mock.sent.size(), "expected exactly one follow-up request");

        var first = mock.sent.get(0).messages();
        var second = mock.sent.get(1).messages();
        // the user prompt appears exactly once in both requests
        long firstUsers = first.stream().filter(m -> "user".equals(m.get("role"))).count();
        long secondUsers = second.stream().filter(m -> "user".equals(m.get("role"))).count();
        assertEquals(1, firstUsers);
        assertEquals(1, secondUsers);

        // the follow-up strictly extends the previous request
        assertEquals(first, second.subList(0, first.size()));
        Map<String, Object> toolResult = second.get(second.size() - 1);
        assertEquals("tool", toolResult.get("role"));
        assertEquals("c1", toolResult.get("tool_call_id"));
    }

    @Test
    void askUserPausesAndAnswerResumes() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("q1", KeYAgentTools.TOOL_ASK_USER,
                "{\"question\":\"split?\",\"options\":[\"yes\",\"no\"]}")),
            ""));
        mock.thenRespond(MockCompletions.text("proceeding with yes"));

        var loop = new AgentLoop(session, mock);
        AgentResult first = loop.begin("tell me", null, null, null);

        assertInstanceOf(AgentResult.NeedsInput.class, first);
        var question = ((AgentResult.NeedsInput) first).question();
        assertEquals("split?", question.text());
        assertEquals(List.of("yes", "no"), question.options());

        AgentResult resumed = loop.answerQuestion("yes");
        assertInstanceOf(AgentResult.Done.class, resumed);
        assertEquals("proceeding with yes", ((AgentResult.Done) resumed).content());

        // the resumed request carries the tool result with the matching tool_call_id
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertEquals("tool", toolMsg.get("role"));
        assertEquals("q1", toolMsg.get("tool_call_id"));
        assertTrue(String.valueOf(toolMsg.get("content")).contains("yes"));
    }

    @Test
    void approvalPausesAndApprovedToolRuns() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("a1", TestMcpToolProvider.NEEDS_APPROVAL, "{}")), ""));
        mock.thenRespond(MockCompletions.text("done"));

        var loop = new AgentLoop(session, mock);
        AgentResult first = loop.begin("run it", null, null, null);

        assertInstanceOf(AgentResult.NeedsApproval.class, first);
        var call = ((AgentResult.NeedsApproval) first).toolCall();
        assertEquals(TestMcpToolProvider.NEEDS_APPROVAL, call.name());
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty(), "tool must not run before approval");

        AgentResult resumed = loop.decideApproval(true, false);
        assertInstanceOf(AgentResult.Done.class, resumed);
        assertEquals(1, TestMcpToolProvider.EXECUTED.size());
        assertTrue(
            TestMcpToolProvider.EXECUTED.get(0).startsWith(TestMcpToolProvider.NEEDS_APPROVAL));
    }

    @Test
    void deniedToolIsReportedToTheModel() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("a1", TestMcpToolProvider.NEEDS_APPROVAL, "{}")), ""));
        mock.thenRespond(MockCompletions.text("understood"));

        var loop = new AgentLoop(session, mock);
        loop.begin("run it", null, null, null);
        AgentResult resumed = loop.decideApproval(false, false);

        assertInstanceOf(AgentResult.Done.class, resumed);
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty(), "denied tool must not run");
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("denied"));
    }

    @Test
    void useSkillIsGatedByTheSettingsFlag() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_USE_SKILL,
                "{\"name\":\"optics\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("go", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertNull(session.getActiveSkill(), "skill must not be activated while the flag is off");
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertEquals("s1", toolMsg.get("tool_call_id"));
        assertTrue(String.valueOf(toolMsg.get("content")).contains("disabled"));
    }

    @Test
    void useSkillRejectsUnknownSkill() {
        LlmSettings.INSTANCE.setAgentCanUseSkills(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_USE_SKILL,
                "{\"name\":\"no-such-skill\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("fine"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("go", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertNull(session.getActiveSkill());
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("Unknown skill"));
    }

    /** Scripted {@link ChatCompletionsClient}. */
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
