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
 * Headless metadata and parameter-validation tests for the nine proof-script tools added on top of
 * {@code tryclose}/{@code auto}: {@code run_macro}, {@code run_smt}, {@code simplify_goal} (AUTO
 * automation; the first two backgroundable) and the six ASK-approval rule-surgery tools. The
 * {@code goal}/{@code proof} parameters are present everywhere, single-goal tools reject {@code
 * "all"}, and the error branches return informative strings without touching a live proof.
 */
class ProofToolMetadataTest {

    private static AgentTool tool(List<AgentTool> tools, String name) {
        return tools.stream().filter(t -> t.name().equals(name)).findFirst().orElseThrow();
    }

    private static List<AgentTool> all() {
        var tools = new java.util.ArrayList<AgentTool>();
        tools.addAll(new ProofAutomationTools().get());
        tools.addAll(new RuleSurgeryTools().get());
        return tools;
    }

    @Test
    void tautomationToolsAreProofAutoWithTheRightBackgroundFlags() {
        var tools = all();
        var macro = tool(tools, ProofAutomationTools.TOOL_RUN_MACRO);
        var smt = tool(tools, ProofAutomationTools.TOOL_RUN_SMT);
        var simplify = tool(tools, ProofAutomationTools.TOOL_SIMPLIFY_GOAL);
        for (var t : List.of(macro, smt, simplify)) {
            assertEquals(ToolCategory.PROOF, t.category());
            assertEquals(Tool.ApprovalRequirement.AUTO, t.approval());
        }
        assertTrue(macro.backgroundable(), "run_macro must be backgroundable");
        assertTrue(smt.backgroundable(), "run_smt must be backgroundable");
        assertFalse(simplify.backgroundable(), "simplify_goal must not be backgroundable");
    }

    @Test
    void ruleSurgeryToolsAreProofAskAndSynchronous() {
        var tools = all();
        for (var name : List.of(RuleSurgeryTools.TOOL_APPLY_RULE,
            RuleSurgeryTools.TOOL_INSTANTIATE_QUANTIFIER, RuleSurgeryTools.TOOL_WITNESS_CONSTANT,
            RuleSurgeryTools.TOOL_CUT_FORMULA, RuleSurgeryTools.TOOL_EXPAND_DEFINITIONS,
            RuleSurgeryTools.TOOL_REWRITE_TERM)) {
            var t = tool(tools, name);
            assertEquals(ToolCategory.PROOF, t.category(), name);
            assertEquals(Tool.ApprovalRequirement.ASK, t.approval(), name);
            assertFalse(t.backgroundable(), name + " must not be backgroundable");
        }
    }

    @Test
    void everyNewProofToolCarriesGoalAndProofParameters() {
        var tools = all();
        for (var t : tools) {
            var properties = t.parameters().properties();
            assertNotNull(properties, t.name());
            assertTrue(properties.containsKey("goal"), t.name() + " must have a goal parameter");
            assertTrue(properties.containsKey("proof"), t.name() + " must have a proof parameter");
        }
    }

    @Test
    void runMacroEnumeratesTheCuratedMacrosAndRequiresMacro() {
        var tool = tool(all(), ProofAutomationTools.TOOL_RUN_MACRO);
        var macro = tool.parameters().properties().get("macro");
        assertEquals(List.of("symbex", "symbex-only", "onestep", "tryclose-sidebranches",
            "split-prop", "nosplit-prop", "simp-int", "simp-heap", "simp-upd", "transcendental",
            "autopilot"), macro.enumValues());
        assertEquals(List.of("macro"), tool.parameters().required());
    }

    @Test
    void requiredArgumentsOfTheRuleSurgeryTools() {
        var tools = all();
        assertEquals(List.of("taclet"), tool(tools, RuleSurgeryTools.TOOL_APPLY_RULE)
                .parameters().required());
        assertEquals(List.of("with"), tool(tools, RuleSurgeryTools.TOOL_INSTANTIATE_QUANTIFIER)
                .parameters().required());
        assertEquals(List.of("formula", "as"), tool(tools, RuleSurgeryTools.TOOL_WITNESS_CONSTANT)
                .parameters().required());
        assertEquals(List.of("formula"), tool(tools, RuleSurgeryTools.TOOL_CUT_FORMULA)
                .parameters().required());
        var expandRequired = tool(tools, RuleSurgeryTools.TOOL_EXPAND_DEFINITIONS)
                .parameters().required();
        assertTrue(expandRequired == null || expandRequired.isEmpty(),
            "expand_definitions must not mark any parameter as required");
        assertEquals(List.of("find", "replace"), tool(tools, RuleSurgeryTools.TOOL_REWRITE_TERM)
                .parameters().required());
    }

    @Test
    void runMacroRejectsUnknownMacrosBeforeRunning() throws Exception {
        var tool = tool(all(), ProofAutomationTools.TOOL_RUN_MACRO);
        var result = (String) tool.call(Map.of("macro", "close-magic"));
        assertTrue(result.startsWith("Error: unknown macro close-magic"), result);
        assertTrue(result.contains("symbex"), "the error should name the valid choices");
    }

    @Test
    void simplifyGoalRejectsAllGoals() throws Exception {
        var tool = tool(all(), ProofAutomationTools.TOOL_SIMPLIFY_GOAL);
        var result = (String) tool.call(Map.of("goal", "all"));
        assertEquals("Error: simplify_goal acts on a single goal: use \"branch\" or an index,"
            + " not \"all\".", result);
    }

    @Test
    void ruleSurgeryToolsRejectAllGoals() throws Exception {
        var tools = all();
        // required arguments are supplied so that only the goal-targeting error can fire
        var argsByName = Map.of(
            RuleSurgeryTools.TOOL_APPLY_RULE, Map.<String, Object>of("taclet", "foo"),
            RuleSurgeryTools.TOOL_INSTANTIATE_QUANTIFIER, Map.<String, Object>of("with", "x"),
            RuleSurgeryTools.TOOL_WITNESS_CONSTANT,
            Map.<String, Object>of("formula", "\\forall int x; true", "as", "w"),
            RuleSurgeryTools.TOOL_CUT_FORMULA, Map.<String, Object>of("formula", "true"),
            RuleSurgeryTools.TOOL_EXPAND_DEFINITIONS, Map.<String, Object>of("target", "foo()"),
            RuleSurgeryTools.TOOL_REWRITE_TERM,
            Map.<String, Object>of("find", "x", "replace", "y"));
        for (var name : argsByName.keySet()) {
            var t = tool(tools, name);
            var callArgs = new java.util.HashMap<>(argsByName.get(name));
            callArgs.put("goal", "all");
            var result = (String) t.call(callArgs);
            assertEquals("Error: " + name + " acts on a single goal: use \"branch\" or an index,"
                + " not \"all\".", result, name);
        }
    }

    @Test
    void expandDefinitionsNeedsATargetOrFormula() throws Exception {
        var tool = tool(all(), RuleSurgeryTools.TOOL_EXPAND_DEFINITIONS);
        var result = (String) tool.call(Map.of());
        assertEquals("Error: expand_definitions needs one of 'target' or 'formula'", result);
    }

    @Test
    void goalAndProofAreNeverRequired() {
        for (var t : all()) {
            var required = t.parameters().required();
            assertFalse(required != null && required.contains("goal"), t.name());
            assertFalse(required != null && required.contains("proof"), t.name());
        }
    }
}
