/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;
import java.util.Map;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless metadata and parameter-validation tests for the Tier-3 tool set: the guarded
 * multi-step runner, the sandboxed side-proof probes, forking, orientation and sequent-editing
 * tools. Error branches that need no live proof are exercised here.
 */
class Tier3ToolMetadataTest {

    private static AgentTool tool(List<AgentTool> tools, String name) {
        return tools.stream().filter(t -> t.name().equals(name)).findFirst().orElseThrow();
    }

    private static List<AgentTool> all() {
        var tools = new java.util.ArrayList<AgentTool>();
        tools.addAll(new ExploreProofTools().get());
        tools.addAll(new ScriptSequenceTools().get());
        tools.addAll(new ProofOrientationTools().get());
        tools.addAll(new SequentEditingTools().get());
        tools.addAll(new ProofForkTools().get());
        return tools;
    }

    @Test
    void explorationProbesAreAutoAndBackgroundable() {
        for (var name : List.of(ExploreProofTools.TOOL_EXPLORE_ASSUMPTION,
            ExploreProofTools.TOOL_EXPLORE_FORMULA)) {
            var t = tool(all(), name);
            assertEquals(ToolCategory.PROOF, t.category(), name);
            assertEquals(Tool.ApprovalRequirement.AUTO, t.approval(), name);
            assertTrue(t.backgroundable(),
                name + " runs an isolated side proof and must be backgroundable");
        }
    }

    @Test
    void mutatingTier3ToolsAreAskAndSynchronous() {
        for (var name : List.of(ScriptSequenceTools.TOOL_RUN_SCRIPT,
            SequentEditingTools.TOOL_HIDE_SEQUENT, SequentEditingTools.TOOL_UNHIDE_SEQUENT,
            SequentEditingTools.TOOL_FOCUS_GOAL, SequentEditingTools.TOOL_LET_ABBREV,
            ProofForkTools.TOOL_FORK_PROOF)) {
            var t = tool(all(), name);
            assertEquals(ToolCategory.PROOF, t.category(), name);
            assertEquals(Tool.ApprovalRequirement.ASK, t.approval(), name);
            assertFalse(t.backgroundable(), name + " must not be backgroundable");
        }
    }

    @Test
    void orientationToolsAreAutoReadOnly() {
        for (var name : List.of(ProofOrientationTools.TOOL_LIST_BRANCHES,
            ProofOrientationTools.TOOL_ASSERT_OPEN_GOALS)) {
            var t = tool(all(), name);
            assertEquals(ToolCategory.PROOF, t.category(), name);
            assertEquals(Tool.ApprovalRequirement.AUTO, t.approval(), name);
            assertFalse(t.backgroundable(), name + " is read-only, no backgrounding");
        }
    }

    @Test
    void requiredParametersOfTheTier3Tools() {
        var tools = all();
        assertEquals(List.of("steps"), tool(tools, ScriptSequenceTools.TOOL_RUN_SCRIPT)
                .parameters().required());
        assertEquals(List.of("formula"), tool(tools, ExploreProofTools.TOOL_EXPLORE_ASSUMPTION)
                .parameters().required());
        assertEquals(List.of("formula"), tool(tools, ExploreProofTools.TOOL_EXPLORE_FORMULA)
                .parameters().required());
        assertEquals(List.of("expected"),
            tool(tools, ProofOrientationTools.TOOL_ASSERT_OPEN_GOALS).parameters().required());
        assertEquals(List.of("sequent"), tool(tools, SequentEditingTools.TOOL_HIDE_SEQUENT)
                .parameters().required());
        assertEquals(List.of("sequent"), tool(tools, SequentEditingTools.TOOL_UNHIDE_SEQUENT)
                .parameters().required());
        assertEquals(List.of("keep"), tool(tools, SequentEditingTools.TOOL_FOCUS_GOAL)
                .parameters().required());
        assertEquals(List.of("name", "term"), tool(tools, SequentEditingTools.TOOL_LET_ABBREV)
                .parameters().required());
    }

    @Test
    void runScriptHasNoRequiredTopLevelBeyondSteps() {
        var t = tool(all(), ScriptSequenceTools.TOOL_RUN_SCRIPT);
        var required = t.parameters().required();
        assertFalse(required.contains("proof"));
        assertNotNull(t.parameters().properties().get("steps"));
    }

    @Test
    void singleGoalTier3ToolsRejectAllGoals() throws Exception {
        var tools = all();
        var names = List.of(ExploreProofTools.TOOL_EXPLORE_ASSUMPTION,
            ExploreProofTools.TOOL_EXPLORE_FORMULA, ProofForkTools.TOOL_FORK_PROOF,
            SequentEditingTools.TOOL_HIDE_SEQUENT, SequentEditingTools.TOOL_UNHIDE_SEQUENT,
            SequentEditingTools.TOOL_FOCUS_GOAL);
        for (var name : names) {
            var t = tool(tools, name);
            var callArgs = new java.util.HashMap<String, Object>();
            callArgs.put("goal", "all");
            // required schema args are supplied so only the goal-targeting error can fire
            if (name.equals(ExploreProofTools.TOOL_EXPLORE_ASSUMPTION)
                    || name.equals(ExploreProofTools.TOOL_EXPLORE_FORMULA)) {
                callArgs.put("formula", "true");
            }
            if (name.equals(SequentEditingTools.TOOL_HIDE_SEQUENT)
                    || name.equals(SequentEditingTools.TOOL_UNHIDE_SEQUENT)) {
                callArgs.put("sequent", "true ==>");
            }
            if (name.equals(SequentEditingTools.TOOL_FOCUS_GOAL)) {
                callArgs.put("keep", "true ==>");
            }
            var result = (String) t.call(callArgs);
            assertEquals("Error: " + name + " acts on a single goal: use \"branch\" or an index,"
                + " not \"all\".", result, name);
        }
    }

    @Test
    void runScriptValidatesItsStepGuardrails() throws Exception {
        var t = tool(all(), ScriptSequenceTools.TOOL_RUN_SCRIPT);
        // steps must be a list
        assertTrue(((String) t.call(Map.of("steps", "foo"))).startsWith("Error: 'steps'"));
        // empty steps
        assertTrue(((String) t.call(Map.of("steps", List.of()))).startsWith("Error: 'steps'"));
        // more than eight steps
        var tooMany = new java.util.ArrayList<Map<String, Object>>();
        for (int i = 0; i < 9; i++) {
            tooMany.add(Map.of("command", "auto"));
        }
        assertTrue(((String) t.call(Map.of("steps", tooMany)))
                .startsWith("Error: run_script accepts at most 8 steps"),
            "bounded length");
        // unknown command
        assertEquals("Error: run_script step 0: unknown command 'close-magic'; allowed: tryclose,"
            + " auto, macro, smt, oss, apply_rule, instantiate_quantifier, witness_constant,"
            + " cut_formula, expand_definitions, rewrite_term",
            t.call(Map.of("steps", List.of(Map.of("command", "close-magic")))));
        // unknown step parameter
        assertTrue(((String) t.call(Map.of("steps",
            List.of(Map.of("command", "auto", "args", Map.of("bogus", 1))))))
                .contains("unknown parameter 'bogus'"));
        // "all" goal inside a step is rejected
        assertTrue(((String) t.call(Map.of("steps",
            List.of(Map.of("command", "auto", "goal", "all")))))
                .contains("not supported inside run_script"));
    }

    @Test
    void runScriptRejectsUnknownMacroInSteps() throws Exception {
        var t = tool(all(), ScriptSequenceTools.TOOL_RUN_SCRIPT);
        var result = (String) t.call(Map.of("steps",
            List.of(Map.of("command", "macro", "args", Map.of("macro", "bogus")))));
        assertTrue(result.startsWith("Error: run_script step 0 (macro): unknown macro 'bogus'"),
            result);
    }
}
