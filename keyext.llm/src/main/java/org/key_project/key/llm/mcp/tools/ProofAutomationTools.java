/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * The proof automation tools {@code run_macro}, {@code run_smt} and {@code simplify_goal}: they
 * wrap the KeY proof-script commands {@code macro}, {@code smt} and {@code oss} on the selected
 * proof through the same machinery as the "Apply Script" action. All three accept the unified
 * {@code goal} targeting ({@code "branch"}, {@code "all"} or an open-goal index; {@code
 * simplify_goal} restricts itself to a single goal) and an optional {@code proof} identifier from
 * {@code list_proofs}; see {@link ProofScriptRunner}.
 *
 * @author Alexander Weigl
 */
public final class ProofAutomationTools implements AgentToolProvider {
    /** The {@code run_macro} tool. */
    public static final String TOOL_RUN_MACRO = "run_macro";
    /** The {@code run_smt} tool. */
    public static final String TOOL_RUN_SMT = "run_smt";
    /** The {@code simplify_goal} tool. */
    public static final String TOOL_SIMPLIFY_GOAL = "simplify_goal";

    /** The curated macros the {@code run_macro} tool may execute, in schema/enum order. */
    private static final List<String> MACRO_OPTIONS = List.of("symbex", "symbex-only", "onestep",
        "tryclose-sidebranches", "split-prop", "nosplit-prop", "simp-int", "simp-heap", "simp-upd",
        "transcendental", "autopilot");

    /** The same macros as a set, for validating the {@code macro} argument. */
    private static final Set<String> MACROS = Set.copyOf(MACRO_OPTIONS);

    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(TOOL_RUN_MACRO, ToolCategory.PROOF,
                "Runs a curated KeY proof macro - the `macro` proof-script command - on the"
                    + " targeted goals: symbolic execution (symbex, symbex-only), propositional"
                    + " splitting (split-prop, nosplit-prop), simplification (onestep, simp-int,"
                    + " simp-heap, simp-upd), closing side branches (tryclose-sidebranches), SMT"
                    + " for transcendental goals (transcendental) or the full automation pilot"
                    + " (autopilot). Targets the first open goal of the current branch (default),"
                    + " all open goals, or a single goal by index; can run in the background, so"
                    + " you can keep asking questions while it works.",
                JsonSchema.builder().withType("object")
                        .addProperty("macro",
                            JsonSchema.builder().withType("string").withEnum(MACRO_OPTIONS)
                                    .withDescription("the macro to run: symbex (finish symbolic"
                                        + " execution), symbex-only (symbolic execution, no"
                                        + " branching), onestep (apply the one-step simplifier),"
                                        + " tryclose-sidebranches (close the side branches),"
                                        + " split-prop (full propositional expansion with splitting),"
                                        + " nosplit-prop (propositional expansion without splitting),"
                                        + " simp-int (simplify integer arithmetic), simp-heap"
                                        + " (simplify heap formulas), simp-upd (simplify updates),"
                                        + " transcendental (prove transcendental goals with SMT),"
                                        + " autopilot (full automation pilot)")
                                    .build())
                        .addProperty("goal",
                            JsonSchema.builder().withType("string")
                                    .withDescription(ProofScriptTools.GOAL_DESCRIPTION).build())
                        .addProperty("proof",
                            JsonSchema.builder().withType("string")
                                    .withDescription(
                                        "proof identifier from list_proofs; defaults to"
                                            + " the selected proof")
                                    .build())
                        .addRequired("macro")
                        .build(),
                true,
                args -> {
                    var name = AgentTool.stringArg(args, "macro");
                    if (name == null || name.isBlank() || !MACROS.contains(name)) {
                        return "Error: unknown macro " + name + "; choose from: symbex,"
                            + " symbex-only, onestep, tryclose-sidebranches, split-prop,"
                            + " nosplit-prop, simp-int, simp-heap, simp-upd, transcendental,"
                            + " autopilot";
                    }
                    var command = new ScriptCommandAst("macro", Map.of(), List.of(name));
                    var commands = ProofScriptRunner.target(
                        ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal")), command);
                    return ProofScriptRunner.run(args, "run_macro", commands);
                }),
            AgentTool.tool(TOOL_RUN_SMT, ToolCategory.PROOF,
                "Runs KeY's SMT solver integration - the `smt` proof-script command - on the"
                    + " targeted goals: goals the solver proves valid are closed automatically."
                    + " Targets the first open goal of the current branch (default), all open"
                    + " goals, or a single goal by index; solver runs may take a while, so this"
                    + " can run in the background.",
                AgentTool.schema(
                    "solver",
                    JsonSchema.builder().withType("string")
                            .withDescription("the SMT solver to use; defaults to Z3 (Z3, CVC4,"
                                + " Vampire, Princess, ... depending on the installed solvers)")
                            .build(),
                    "timeout",
                    JsonSchema.builder().withType("integer")
                            .withDescription("solver timeout in seconds").build(),
                    "goal",
                    JsonSchema.builder().withType("string")
                            .withDescription(ProofScriptTools.GOAL_DESCRIPTION).build(),
                    "proof",
                    JsonSchema.builder().withType("string")
                            .withDescription("proof identifier from list_proofs; defaults to the"
                                + " selected proof")
                            .build()),
                true,
                args -> {
                    var named = new HashMap<String, Object>();
                    var solver = AgentTool.stringArg(args, "solver");
                    if (solver != null && !solver.isBlank()) {
                        named.put("solver", solver);
                    }
                    var timeout = AgentTool.intArg(args, "timeout");
                    if (timeout != null && timeout >= 0) {
                        named.put("timeout", timeout);
                    }
                    var command = new ScriptCommandAst("smt", named, List.of());
                    var commands =
                        switch (ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal"))) {
                            case ProofScriptRunner.All all -> {
                                named.put("all", true);
                                yield List.of(command);
                            }
                            case ProofScriptRunner.Index idx ->
                                List.of(ProofScriptRunner.selectGoal(idx.number()), command);
                            case ProofScriptRunner.Branch branch -> List.of(command);
                        };
                    return ProofScriptRunner.run(args, "run_smt", commands);
                }),
            AgentTool.tool(TOOL_SIMPLIFY_GOAL, ToolCategory.PROOF,
                "Applies KeY's one-step simplifier - the `oss` proof-script command - to a single"
                    + " goal, optionally restricted to the antecedent, the succedent, or only the"
                    + " recently added or changed formulas. Acts on a single goal only: \"branch\""
                    + " (the default) or an open-goal index.",
                AgentTool.schema(
                    "antecedent",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("simplify the antecedent (default true)").build(),
                    "succedent",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("simplify the succedent (default true)").build(),
                    "recent_only",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("simplify only the recently added or changed formulas"
                                + " (default false; overrides antecedent and succedent)")
                            .build(),
                    "goal",
                    JsonSchema.builder().withType("string")
                            .withDescription(ProofScriptTools.GOAL_DESCRIPTION).build(),
                    "proof",
                    JsonSchema.builder().withType("string")
                            .withDescription("proof identifier from list_proofs; defaults to the"
                                + " selected proof")
                            .build()),
                false,
                args -> {
                    var goal = ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal"));
                    if (goal instanceof ProofScriptRunner.All) {
                        return "Error: simplify_goal acts on a single goal: use \"branch\" or an"
                            + " index, not \"all\".";
                    }
                    var named = new HashMap<String, Object>();
                    if (args.containsKey("antecedent") && !AgentTool.boolArg(args, "antecedent")) {
                        named.put("antecedent", false);
                    }
                    if (args.containsKey("succedent") && !AgentTool.boolArg(args, "succedent")) {
                        named.put("succedent", false);
                    }
                    if (AgentTool.boolArg(args, "recent_only")) {
                        named.put("recentOnly", true);
                    }
                    var command = new ScriptCommandAst("oss", named, List.of());
                    var commands = switch (goal) {
                        case ProofScriptRunner.Index idx ->
                            List.of(ProofScriptRunner.selectGoal(idx.number()), command);
                        default -> List.of(command);
                    };
                    return ProofScriptRunner.run(args, "simplify_goal", commands);
                }));
    }
}
