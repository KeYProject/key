/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.key_project.key.llm.LlmContext.LlmMessage;
import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the request assembly in {@link ExtendedPrompt}: message order, tool advertisement and the
 * history budget.
 */
class ExtendedPromptTest {

    private LlmSession session;

    @BeforeEach
    void setUp() {
        session = new LlmSession("https://example.invalid", "token", "model");
        LlmSettings.INSTANCE.setMaxHistoryMessages(30);
        LlmSettings.INSTANCE.setMaxHistoryChars(32000);
        LlmSettings.INSTANCE.setMaxToolRounds(8);
        LlmSettings.INSTANCE.setToolsDisabled(new TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new TreeSet<>());
        LlmSettings.INSTANCE.setSendTemperature(false);
        LlmSettings.INSTANCE.setSendMaxOutputTokens(false);
        session.setAttachProofContext(false);
    }

    private static List<String> roles(List<Map<String, Object>> messages) {
        return messages.stream().map(m -> String.valueOf(m.get("role"))).toList();
    }

    /** The advertised tool names of a request. */
    private static Set<String> toolNames(AgentRequest request) {
        var names = new java.util.LinkedHashSet<String>();
        for (var t : request.tools()) {
            names.add(String.valueOf(((Map<?, ?>) t.get("function")).get("name")));
        }
        return names;
    }

    @Test
    void minimalRequestHasSystemAndUser() {
        var request = ExtendedPrompt.build(session, null, null, "hello there", null);
        assertEquals(2, request.messages().size());
        assertEquals(List.of("system", "user"), roles(request.messages()));
        assertEquals("hello there", request.messages().get(1).get("content"));
        assertEquals("model", request.model());
    }

    @Test
    void advertisesTheStandardToolsButNoKeySpecificToolsByDefault() {
        var request = ExtendedPrompt.build(session, null, null, "hi", null);
        var toolNames = toolNames(request);
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_LIST_TOOLS));
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_GLOB));
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_READ));
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_EDIT));
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_SHELL));
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_QUESTION));
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_SKILL));
        assertTrue(toolNames.contains(KeYAgentTools.TOOL_SUBAGENT));
        assertTrue(toolNames.contains(TestMcpToolProvider.ECHO));
        // the KeY-specific tools (Proof/Taclets) are loaded on request via list_tools
        assertTrue(!toolNames.contains(KeYAgentTools.TOOL_GET_PROOF_CONTEXT));
        assertTrue(!toolNames.contains(KeYAgentTools.TOOL_TRYCLOSE));
        assertTrue(!toolNames.contains(KeYAgentTools.TOOL_LIST_TACLETS));
    }

    @Test
    void skillWhitelistRestrictsAdvertisedToolsAndAddsInstructions() {
        var whitelist = List.of(KeYAgentTools.TOOL_READ, KeYAgentTools.TOOL_SHELL);
        var skill = new Skill("lockdown", "read-only review", "Only read the model files.",
            whitelist, true);
        var request = ExtendedPrompt.build(session, null, null, "hi", skill);
        assertEquals(Set.copyOf(whitelist), toolNames(request),
            "only the whitelisted standard tools may be offered while the skill is active");
        String sys = String.valueOf(request.messages().get(0).get("content"));
        assertTrue(sys.contains("# Active skill: lockdown"), sys);
        assertTrue(sys.contains("Only read the model files."), sys);
    }

    @Test
    void skillWithoutToolWhitelistKeepsTheFullStandardToolSet() {
        var skill = new Skill("coach", "hints only", "Give hints.", List.of(), true);
        var request = ExtendedPrompt.build(session, null, null, "hi", skill);
        assertTrue(toolNames(request).contains(KeYAgentTools.TOOL_SHELL));
        assertTrue(toolNames(request).contains(KeYAgentTools.TOOL_QUESTION));
        assertTrue(toolNames(request).contains(TestMcpToolProvider.ECHO));
        assertTrue(!toolNames(request).contains(KeYAgentTools.TOOL_TRYCLOSE));
    }

    @Test
    void disabledToolsAreNotAdvertised() {
        LlmSettings.INSTANCE
                .setToolsDisabled(new TreeSet<>(Set.of(KeYAgentTools.TOOL_SHELL)));
        var request = ExtendedPrompt.build(session, null, null, "hi", null);
        assertTrue(
            request.tools().stream().map(t -> (String) ((Map<?, ?>) t.get("function")).get("name"))
                    .noneMatch(KeYAgentTools.TOOL_SHELL::equals));
        // approval of the disabled tool is not revoked by accident
        assertTrue(LlmSettings.INSTANCE.getAllowedToolsWithApproval().isEmpty());
    }

    @Test
    void proofContextToggleAddsContextBlock() {
        session.setAttachProofContext(true);
        var request = ExtendedPrompt.build(session, null, null, "hi", null);
        assertEquals(List.of("system", "system", "user"), roles(request.messages()));
        String sys = String.valueOf(request.messages().get(1).get("content"));
        assertTrue(sys.contains("no proof loaded"), sys);

        session.setAttachProofContext(false);
        var off = ExtendedPrompt.build(session, null, null, "hi", null);
        assertEquals(2, off.messages().size());
    }

    @Test
    void historyIsCappedByMessageCount() {
        LlmSettings.INSTANCE.setMaxHistoryMessages(5);
        for (int i = 0; i < 12; i++) {
            session.getContext().addMessage(
                i % 2 == 0 ? LlmMessage.user("message " + i)
                        : LlmMessage.assistant("message " + i));
        }
        var request = ExtendedPrompt.build(session, null, null, "next", null);
        var msgs = request.messages();
        assertEquals("system", msgs.get(0).get("role"));
        assertEquals("user", msgs.get(msgs.size() - 1).get("role"));
        assertEquals("next", msgs.get(msgs.size() - 1).get("content"));
        int historyCount = msgs.size() - 2;
        assertTrue(historyCount <= 5, "expected at most 5 history messages, got " + historyCount);
        // the newest history messages are kept
        String lastHistory = String.valueOf(msgs.get(msgs.size() - 2).get("content"));
        assertTrue(lastHistory.contains("11"), lastHistory);
    }

    @Test
    void historyIsCappedByCharacterBudget() {
        LlmSettings.INSTANCE.setMaxHistoryChars(10);
        for (int i = 0; i < 6; i++) {
            session.getContext().addMessage(LlmMessage.user("aaaaaaaaaa"));
            session.getContext().addMessage(LlmMessage.assistant("bbbbbbbbbb"));
        }
        var request = ExtendedPrompt.build(session, null, null, "next", null);
        var msgs = request.messages();
        int historyCount = msgs.size() - 2;
        assertTrue(historyCount <= 2, "expected at most 2 history messages (10 chars budget)");
    }
}
