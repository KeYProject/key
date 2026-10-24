/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;

import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the {@code ask_llm} self-consultation tool: {@link AskLlmRunner} performs a fresh
 * one-shot completion with a clean context (no history, no tools) and delivers the reply, the
 * agent loop intercepts the call without the dispatch lock (and reports it when disabled in the
 * settings), and sub-agent child loops can consult the LLM as well. A scripted
 * {@link ChatCompletionsClient} supplies the canned replies.
 */
class AskLlmTest {

    private LlmSession session;

    @BeforeEach
    void setUp() {
        LlmSettings.INSTANCE.setMaxToolRounds(8);
        LlmSettings.INSTANCE.setMaxSubagentTurns(4);
        LlmSettings.INSTANCE.setMaxSubagentDepth(2);
        LlmSettings.INSTANCE.setMaxParallelSubagents(4);
        LlmSettings.INSTANCE.setSubagentsEnabled(false);
        LlmSettings.INSTANCE.setAskLlmEnabled(true);
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setToolsDisabled(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setAgentCanUseSkills(false);
        TestMcpToolProvider.reset();
        session = new LlmSession("https://example.invalid", "token", "model");
    }

    // ------------------------------------------------------------------ AskLlmRunner unit tests

    @Test
    void freshContextReplyIsDeliveredToTheCaller() {
        var mock = new SubagentLoopTest.MockCompletions();
        mock.thenRespond(SubagentLoopTest.MockCompletions.text("the plan is sound"));

        var result = AskLlmRunner.run(session, mock, "{\"prompt\":\"reflect on my plan\"}");

        assertTrue(result.contains("fresh-context reply"), result);
        assertTrue(result.contains("the plan is sound"), result);
        assertEquals(1, mock.sent.size());
        var request = mock.sent.get(0);
        // a clean, tool-free context: only the prompt as the single user message
        assertEquals("model", request.model());
        assertTrue(request.tools().isEmpty());
        assertEquals(1, request.messages().size());
        assertEquals("user", request.messages().get(0).get("role"));
        assertEquals("reflect on my plan", request.messages().get(0).get("content"));
    }

    @Test
    void systemPromptAndModelOverrideReachTheFreshRequest() {
        var mock = new SubagentLoopTest.MockCompletions();
        mock.thenRespond(SubagentLoopTest.MockCompletions.text("ok"));

        AskLlmRunner.run(session, mock,
            "{\"prompt\":\"check\",\"system\":\"you are a critic\",\"model\":\"o3-mini\"}");

        var request = mock.sent.get(0);
        assertEquals("o3-mini", request.model());
        assertEquals(2, request.messages().size());
        assertEquals("system", request.messages().get(0).get("role"));
        assertEquals("you are a critic", request.messages().get(0).get("content"));
        assertEquals("user", request.messages().get(1).get("role"));
    }

    @Test
    void blankPromptIsRejectedWithoutCallingTheClient() {
        var mock = new SubagentLoopTest.MockCompletions();
        var result = AskLlmRunner.run(session, mock, "{\"prompt\":\"   \"}");

        assertEquals("[ask_llm: the 'prompt' parameter must not be empty]", result);
        assertTrue(mock.sent.isEmpty(), "no completion may be made for a blank prompt");
    }

    @Test
    void clientFailureIsReportedAsErrorText() {
        ChatCompletionsClient failing = (s, r) -> {
            throw new RuntimeException("boom");
        };
        var result = AskLlmRunner.run(session, failing, "{\"prompt\":\"think\"}");

        assertTrue(result.startsWith("[ask_llm failed:"), result);
        assertTrue(result.contains("boom"), result);
    }

    // ------------------------------------------------------------------ parent loop interception

    @Test
    void askLlmRunsFreshCompletionInTheParentLoop() {
        var mock = new SubagentLoopTest.MockCompletions();
        mock.thenRespond(SubagentLoopTest.MockCompletions.toolCalls(
            List.of(SubagentLoopTest.MockCompletions.tool("a1", KeYAgentTools.TOOL_ASK_LLM,
                "{\"prompt\":\"reflect on my plan\"}")),
            ""));
        mock.thenRespond(SubagentLoopTest.MockCompletions.text("the plan is sound"));
        mock.thenRespond(SubagentLoopTest.MockCompletions.text("proceeding"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("help me", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        assertTrue(((AgentResult.Done) result).content().contains("proceeding"));

        // three requests: parent turn, the fresh ask_llm completion, the parent continuation
        assertEquals(3, mock.sent.size());
        var fresh = mock.sent.get(1);
        assertEquals("model", fresh.model());
        assertTrue(fresh.tools().isEmpty(), "the fresh context must not see tools");
        assertEquals(List.of("reflect on my plan"),
            fresh.messages().stream().map(m -> String.valueOf(m.get("content"))).toList());
        // the reply is delivered back to the parent's thread as the tool result
        var parentFollowUp = mock.sent.get(2).messages();
        var last = parentFollowUp.get(parentFollowUp.size() - 1);
        assertEquals("tool", last.get("role"));
        assertTrue(String.valueOf(last.get("content")).contains("the plan is sound"));
    }

    @Test
    void askLlmDisabledBySettingsIsReportedToTheModel() {
        LlmSettings.INSTANCE.setAskLlmEnabled(false);
        var mock = new SubagentLoopTest.MockCompletions();
        mock.thenRespond(SubagentLoopTest.MockCompletions.toolCalls(
            List.of(SubagentLoopTest.MockCompletions.tool("a1", KeYAgentTools.TOOL_ASK_LLM,
                "{\"prompt\":\"reflect\"}")),
            ""));
        mock.thenRespond(SubagentLoopTest.MockCompletions.text("understood"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("go", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        // no nested completion was made, the gate answer went back into the thread
        assertEquals(2, mock.sent.size());
        var followUp = mock.sent.get(1).messages();
        var last = followUp.get(followUp.size() - 1);
        assertEquals("tool", last.get("role"));
        assertTrue(String.valueOf(last.get("content")).contains("disabled in the settings"));
    }

    // ------------------------------------------------------------------ sub-agent child loop

    @Test
    void subAgentCanConsultTheLlm() {
        LlmSettings.INSTANCE.setSubagentsEnabled(true);
        var mock = new SubagentLoopTest.MockCompletions();
        mock.thenRespond(SubagentLoopTest.MockCompletions.toolCalls(
            List.of(SubagentLoopTest.MockCompletions.tool("s1", KeYAgentTools.TOOL_SPAWN_SUBAGENT,
                "{\"role\":\"" + TestSubagentRoleProvider.ASK_LLM_ROLE
                    + "\",\"task\":\"review my plan\"}")),
            ""));
        // the child consults a fresh LLM instance and then answers on that basis
        mock.thenRespond(SubagentLoopTest.MockCompletions.toolCalls(
            List.of(SubagentLoopTest.MockCompletions.tool("c1", KeYAgentTools.TOOL_ASK_LLM,
                "{\"prompt\":\"child reflection\"}")),
            ""));
        mock.thenRespond(SubagentLoopTest.MockCompletions.text("the child reflection says: ok"));
        mock.thenRespond(SubagentLoopTest.MockCompletions
                .text("KEY_AGENT_RESULT {\"summary\":\"reviewed\"}\nchild says ok"));
        mock.thenRespond(SubagentLoopTest.MockCompletions.text("parent done"));

        var loop = new AgentLoop(session, mock);
        AgentResult result = loop.begin("delegate", null, null, null);

        assertInstanceOf(AgentResult.Done.class, result);
        // four requests: parent, child, fresh ask_llm completion, child final, parent final
        assertEquals(5, mock.sent.size(), "expected 5 requests, got "
            + mock.sent.stream().map(r -> r.messages().toString()).toList());
        var fresh = mock.sent.get(2);
        assertTrue(fresh.tools().isEmpty(), "the child's fresh context must not see tools");
        assertEquals(List.of("child reflection"),
            fresh.messages().stream().map(m -> String.valueOf(m.get("content"))).toList());
        // the child's follow-up carried the fresh reply into its thread
        var childFollowUp = mock.sent.get(3).messages();
        var last = childFollowUp.get(childFollowUp.size() - 1);
        assertTrue(String.valueOf(last.get("content")).contains("child reflection says: ok"));
    }
}
