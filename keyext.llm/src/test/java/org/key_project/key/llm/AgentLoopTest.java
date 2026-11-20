/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.time.Duration;
import java.util.ArrayDeque;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
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
            List.of(MockCompletions.tool("q1", KeYAgentTools.TOOL_QUESTION,
                "{\"question\":\"split?\",\"options\":[\"yes\",\"no\"]}")),
            ""));
        mock.thenRespond(MockCompletions.text("proceeding with yes"));

        var loop = new AgentLoop(session, mock);
        AgentResult first = loop.begin("tell me", null, null, null);

        assertInstanceOf(AgentResult.NeedsInput.class, first);
        var question = ((AgentResult.NeedsInput) first).questions().get(0);
        assertEquals("split?", question.text());
        assertEquals(List.of("yes", "no"),
            question.options().stream().map(AgentResult.Question.Option::label).toList());

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
    void executeRequiresApprovalBeforeItRuns() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("e1", KeYAgentTools.TOOL_EXECUTE,
                "{\"code\":\"1+1\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("done"));

        var loop = new AgentLoop(session, mock);
        AgentResult first = loop.begin("run it", null, null, null);

        // execute is ask-approved by default: the turn pauses before any snippet runs
        assertInstanceOf(AgentResult.NeedsApproval.class, first);
        assertEquals(KeYAgentTools.TOOL_EXECUTE,
            ((AgentResult.NeedsApproval) first).toolCall().name());

        // the approval resumes the turn: the approved snippet runs and reports its value
        AgentResult resumed = loop.decideApproval(true, false);
        assertInstanceOf(AgentResult.Done.class, resumed);
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertEquals("2", String.valueOf(toolMsg.get("content")),
            "the approved snippet must run through the JShell path, not the placeholder");
    }

    @Test
    void executeApprovalDenialSkipsTheSnippet() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("e1", KeYAgentTools.TOOL_EXECUTE,
                "{\"code\":\"1+1\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("understood"));

        var loop = new AgentLoop(session, mock);
        loop.begin("run it", null, null, null);
        AgentResult resumed = loop.decideApproval(false, false);

        assertInstanceOf(AgentResult.Done.class, resumed);
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("denied"),
            "the denied snippet must not run: " + toolMsg.get("content"));
    }

    @Test
    void subagentRequiresApprovalBeforeItRuns() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SUBAGENT,
                "{\"agent\":\"echo-role\",\"description\":\"test\",\"prompt\":\"say hi\"}")),
            ""));
        // the child answers immediately without a tool call: its answer ends the delegation
        mock.thenRespond(MockCompletions.text("KEY_AGENT_RESULT {\"summary\":\"hi\"}"));
        mock.thenRespond(MockCompletions.text("done"));

        var loop = new AgentLoop(session, mock);
        AgentResult first = loop.begin("delegate", null, null, null);

        // subagent is ask-approved by default: the turn pauses before the child loop runs
        assertInstanceOf(AgentResult.NeedsApproval.class, first);
        assertEquals(KeYAgentTools.TOOL_SUBAGENT,
            ((AgentResult.NeedsApproval) first).toolCall().name());
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty(),
            "no child tool may run before the approval");

        // the approval resumes the turn: the child loop runs and its answer is the tool result
        AgentResult resumed = loop.decideApproval(true, false);
        assertInstanceOf(AgentResult.Done.class, resumed);
        var lastMessages = mock.sent.get(2).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("hi"),
            "the approved delegation must run the child loop: " + toolMsg.get("content"));
    }

    @Test
    void subagentApprovalDenialSkipsTheChildLoop() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SUBAGENT,
                "{\"agent\":\"echo-role\",\"description\":\"test\",\"prompt\":\"say hi\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("understood"));

        var loop = new AgentLoop(session, mock);
        loop.begin("delegate", null, null, null);
        AgentResult resumed = loop.decideApproval(false, false);

        assertInstanceOf(AgentResult.Done.class, resumed);
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty(), "the child must not run");
        assertEquals(2, mock.sent.size(),
            "the denied delegation must not start a child loop");
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("denied"),
            "the denial is the tool result: " + toolMsg.get("content"));
    }

    @Test
    void subagentWithoutApprovalRequirementRunsDirectly() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(
            new java.util.TreeSet<>(Set.of(KeYAgentTools.TOOL_SUBAGENT)));
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SUBAGENT,
                "{\"agent\":\"echo-role\",\"description\":\"test\",\"prompt\":\"say hi\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("KEY_AGENT_RESULT {\"summary\":\"hi\"}"));
        mock.thenRespond(MockCompletions.text("done"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("hi"),
            "the delegation ran without the approval pause: " + toolMsg.get("content"));
    }

    @Test
    void executeRunsWhileTheDispatchLockIsHeld() throws Exception {
        // the snippet must not wait for the dispatch lock: another session could hold it for
        // a whole tool call (or a parallel sub-agent for many)
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(
            new java.util.TreeSet<>(Set.of(KeYAgentTools.TOOL_EXECUTE)));
        var lockHeld = new CountDownLatch(1);
        var releaseLock = new CountDownLatch(1);
        Thread holder = new Thread(() -> ToolDispatcher.INSTANCE.callSynchronized(() -> {
            lockHeld.countDown();
            try {
                releaseLock.await(30, TimeUnit.SECONDS);
            } catch (InterruptedException ignored) {
                // released early
            }
            return null;
        }), "dispatch-lock-holder");
        holder.start();
        try {
            assertTrue(lockHeld.await(5, TimeUnit.SECONDS), "the holder must have the lock");

            var mock = new MockCompletions();
            mock.thenRespond(MockCompletions.toolCalls(
                List.of(MockCompletions.tool("e1", KeYAgentTools.TOOL_EXECUTE,
                    "{\"code\":\"1+1\"}")),
                ""));
            mock.thenRespond(MockCompletions.text("done"));
            var loop = new AgentLoop(session, mock);

            AgentResult result = assertTimeoutPreemptively(Duration.ofSeconds(20),
                () -> loop.begin("run it", null, null, null),
                "execute must run outside the dispatch lock (the holder keeps it busy)");
            assertInstanceOf(AgentResult.Done.class, result);
        } finally {
            releaseLock.countDown();
            holder.join(TimeUnit.SECONDS.toMillis(5));
        }
    }

    @Test
    void questionAcceptsSeveralQuestions() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("q1", KeYAgentTools.TOOL_QUESTION,
                "{\"questions\":[{\"question\":\"First?\"},{\"header\":\"Mode\","
                    + "\"question\":\"Second?\",\"multiple\":true,"
                    + "\"options\":[{\"label\":\"A\",\"description\":\"first\"},\"B\"]}]}")),
            ""));
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("ask", null, null, null);

        assertInstanceOf(AgentResult.NeedsInput.class, result);
        var questions = ((AgentResult.NeedsInput) result).questions();
        assertEquals(2, questions.size());
        assertNull(questions.get(0).header());
        assertEquals("First?", questions.get(0).text());
        assertEquals("Mode", questions.get(1).header());
        assertTrue(questions.get(1).multiple());
        assertEquals(2, questions.get(1).options().size());
        assertEquals("A", questions.get(1).options().get(0).label());
        assertEquals("first", questions.get(1).options().get(0).description());
        assertEquals("B", questions.get(1).options().get(1).label());
    }

    @Test
    void useSkillIsGatedByTheSettingsFlag() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SKILL,
                "{\"id\":\"optics\"}")),
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
            List.of(MockCompletions.tool("s1", KeYAgentTools.TOOL_SKILL,
                "{\"id\":\"no-such-skill\"}")),
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

    @Test
    void skillWhitelistDeniesCallsOutsideTheWhitelist() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{\"x\":1}")), ""));
        mock.thenRespond(MockCompletions.text("done"));
        var skill = new Skill("narrow", "", "",
            List.of(KeYAgentTools.TOOL_GET_PROOF_CONTEXT), true);

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("go", null, null, skill);

        assertInstanceOf(AgentResult.Done.class, result);
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content"))
                .contains("not in the whitelist of skill 'narrow'"),
            String.valueOf(toolMsg.get("content")));
        assertTrue(!String.valueOf(toolMsg.get("content")).contains("echo:"),
            "the tool outside the whitelist must never be dispatched");
    }

    @Test
    void skillWhitelistAllowsWhitelistedCalls() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{\"x\":1}")), ""));
        mock.thenRespond(MockCompletions.text("done"));
        var skill = new Skill("loose", "", "", List.of(TestMcpToolProvider.ECHO), true);

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("go", null, null, skill);

        assertInstanceOf(AgentResult.Done.class, result);
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("echo:{\"x\":1}"),
            "the whitelisted tool call must be dispatched: " + toolMsg.get("content"));
    }

    @Test
    void listToolsLoadsAKeySpecificCategoryForTheNextRound() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("d1", KeYAgentTools.TOOL_LIST_TOOLS,
                "{\"category\":\"proof\"}")),
            ""));
        mock.thenRespond(MockCompletions.text("ready"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("prepare", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var firstTools = toolsOf(mock.sent.get(0));
        assertTrue(firstTools.contains(KeYAgentTools.TOOL_LIST_TOOLS));
        assertTrue(!firstTools.contains(KeYAgentTools.TOOL_TRYCLOSE),
            "proof tools are not advertised before the discovery call");
        var secondTools = toolsOf(mock.sent.get(1));
        assertTrue(secondTools.contains(KeYAgentTools.TOOL_TRYCLOSE),
            "the discovered proof tools must be advertised in the next round");
        assertTrue(!secondTools.contains(KeYAgentTools.TOOL_LIST_TACLETS),
            "only the requested category is loaded, not the whole taclet set");
    }

    @Test
    void listToolsLoadsNamedKeySpecificTools() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("d1", KeYAgentTools.TOOL_LIST_TOOLS,
                "{\"names\":[\"list_taclets\"]}")),
            ""));
        mock.thenRespond(MockCompletions.text("ok"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("prepare", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var secondTools = toolsOf(mock.sent.get(1));
        assertTrue(secondTools.contains(KeYAgentTools.TOOL_LIST_TACLETS),
            "the named taclet tool must be advertised in the next round");
        assertTrue(!secondTools.contains(KeYAgentTools.TOOL_TRYCLOSE),
            "a different proof tool must stay unadvertised");
    }

    @Test
    void keySpecificToolCallWithoutDiscoveryIsDenied() {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", KeYAgentTools.TOOL_TRYCLOSE, "{}")), ""));
        mock.thenRespond(MockCompletions.text("understood"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("close it", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        var lastMessages = mock.sent.get(1).messages();
        var toolMsg = (Map<String, Object>) lastMessages.get(lastMessages.size() - 1);
        assertTrue(String.valueOf(toolMsg.get("content")).contains("not loaded"),
            "a proof tool the model never discovered must be denied: " + toolMsg.get("content"));
    }

    /** The advertised tool names of a request. */
    private static Set<String> toolsOf(AgentRequest request) {
        return request.tools().stream()
                .map(t -> String.valueOf(((Map<?, ?>) t.get("function")).get("name")))
                .collect(java.util.stream.Collectors.toSet());
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
