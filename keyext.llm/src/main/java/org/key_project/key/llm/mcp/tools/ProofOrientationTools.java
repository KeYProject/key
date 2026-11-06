/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.LogicPrinter;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.ToolCategory;
import org.key_project.prover.sequent.Semisequent;

/**
 * Read-only proof orientation helpers: {@code list_branches} enumerates the open automatic goals
 * of a proof - with the branch label and a peek at the first antecedent and succedent formula of
 * each goal, in the order the {@code goal} parameter of the proof tools numbers them - and
 * {@code assert_open_goals} checks the number of open goals. In contrast to the
 * proof-manipulation tools, neither takes a {@code goal} parameter and neither ever mutates the
 * proof: they only resolve the addressed proof (the {@code proof} identifier or the selected
 * proof) and report on it.
 *
 * @author Alexander Weigl
 */
public final class ProofOrientationTools implements AgentToolProvider {
    /** The {@code list_branches} tool. */
    public static final String TOOL_LIST_BRANCHES = "list_branches";
    /** The {@code assert_open_goals} tool. */
    public static final String TOOL_ASSERT_OPEN_GOALS = "assert_open_goals";

    /** Max length of a printed formula segment before it is truncated with "…". */
    private static final int MAX_FORMULA_LENGTH = 80;

    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(TOOL_LIST_BRANCHES, ToolCategory.PROOF,
                "Lists the open goals of a proof in select (goal-index) order - the ordering"
                    + " behind the 'goal' parameter of the proof tools - one line per goal with"
                    + " its branch label and the first antecedent and succedent formula, plus how"
                    + " many further interactive open goals there are. Read-only, the proof is"
                    + " never modified.",
                JsonSchema.builder().withType("object")
                        .addProperty("proof",
                            JsonSchema.builder().withType("string")
                                    .withDescription(
                                        "proof identifier from list_proofs; defaults to"
                                            + " the selected proof")
                                    .build())
                        .build(),
                args -> listBranches(args)),
            AgentTool.tool(TOOL_ASSERT_OPEN_GOALS, ToolCategory.PROOF,
                "Asserts that the proof currently has exactly the expected number of open goals"
                    + " and returns a pass/fail verdict - use it to verify that previous proof"
                    + " tool calls had the intended effect. Read-only, the proof is never"
                    + " modified.",
                JsonSchema.builder().withType("object")
                        .addProperty("expected",
                            JsonSchema.builder().withType("integer")
                                    .withDescription("the number of open goals to check for")
                                    .build())
                        .addProperty("proof",
                            JsonSchema.builder().withType("string")
                                    .withDescription(
                                        "proof identifier from list_proofs; defaults to"
                                            + " the selected proof")
                                    .build())
                        .addRequired("expected")
                        .build(),
                args -> assertOpenGoals(args)));
    }

    private static String listBranches(Map<String, Object> args) {
        var ref = ProofSelector.proofRef(args);
        if (ref.error() != null) {
            return ref.error();
        }
        var proof = ref.proof();
        if (proof == null) {
            return "Error: no proof selected"; // defensive; ProofSelector.proofRef covers this
        }
        var ordered = ProofScriptRunner.goalsInSelectOrder(proof);
        int total = proof.openGoals().size();
        if (ordered.isEmpty()) {
            return "list_branches: no open automatic goals (proof closed or only interactive"
                + " goals remain).";
        }
        var services = proof.getServices();
        var sb = new StringBuilder();
        sb.append("list_branches: ").append(ordered.size())
                .append(" addressable open goal(s) of ").append(total)
                .append(", in select (goal-index) order:\n");
        for (int i = 0; i < ordered.size(); i++) {
            var goal = ordered.get(i);
            var sequent = goal.sequent();
            var nodeInfo = goal.node().getNodeInfo();
            var rawLabel = nodeInfo == null ? null : nodeInfo.getBranchLabel();
            String branch;
            if (rawLabel == null) {
                branch = "?";
            } else if (rawLabel.isBlank()) {
                branch = "unknown";
            } else {
                branch = rawLabel;
            }
            sb.append(i).append(": ").append(branch).append(" | ")
                    .append(firstFormula(sequent.antecedent(), services)).append(" ==> ")
                    .append(firstFormula(sequent.succedent(), services)).append('\n');
        }
        if (total > ordered.size()) {
            sb.append(total - ordered.size())
                    .append(" further interactive open goal(s) (not addressable by index)\n");
        }
        sb.append("Pass an index or \"branch\" as the goal parameter of the proof tools.");
        return sb.toString();
    }

    private static String assertOpenGoals(Map<String, Object> args) {
        var ref = ProofSelector.proofRef(args);
        if (ref.error() != null) {
            return ref.error();
        }
        var proof = ref.proof();
        if (proof == null) {
            return "Error: no proof selected"; // defensive; ProofSelector.proofRef covers this
        }
        Integer expected = AgentTool.intArg(args, "expected");
        if (expected == null) {
            return "Error: 'expected' must be an integer, got: " + args.get("expected");
        }
        int actual = proof.openGoals().size();
        if (actual == expected) {
            return "assert_open_goals: ok — " + actual + " open goal(s), as expected.";
        }
        return "assert_open_goals: FAIL — expected " + expected + " open goal(s), found " + actual
            + ".";
    }

    /** The first formula of a semisequent, printed and truncated; empty when the side is empty. */
    private static String firstFormula(Semisequent semisequent, Services services) {
        if (semisequent.isEmpty()) {
            return "";
        }
        var formula = LogicPrinter.quickPrintTerm((JTerm) semisequent.getFirst().formula(),
            services);
        return truncate(formula, MAX_FORMULA_LENGTH);
    }

    /** Truncates a string to {@code max} characters, appending "…" when longer. */
    private static String truncate(String s, int max) {
        return s.length() <= max ? s : s.substring(0, max) + "…";
    }
}
