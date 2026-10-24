/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ToolCategory;

import org.jspecify.annotations.Nullable;

/**
 * The proof automation tools {@code tryclose} and {@code auto}: they execute the corresponding
 * KeY proof-script commands on the selected proof through the same machinery as the "Apply
 * Script" action. Both accept the unified {@code goal} targeting ({@code "branch"}, {@code "all"}
 * or an open-goal index) and an optional {@code proof} identifier from {@code list_proofs}; see
 * {@link ProofScriptRunner}.
 *
 * @author Alexander Weigl
 */
public final class ProofScriptTools implements AgentToolProvider {
    /** The description shared by every {@code goal} parameter of the automation tools. */
    static final String GOAL_DESCRIPTION = "the target: \"branch\" (first open goal, default),"
        + " \"all\" (all open goals), or a 0-based open-goal index (negative = from the end)";

    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_TRYCLOSE, ToolCategory.PROOF,
                "Applies the KeY proof-script command 'tryclose' to the targeted goals: it"
                    + " automatically tries to close them with the TryClose strategy. Targets"
                    + " either the first open goal of the current branch (default), all open"
                    + " goals, or a single goal by index. May take a while on many goals, so it"
                    + " can run in the background.",
                AgentTool.schema("goal",
                    JsonSchema.builder().withType("string").withDescription(GOAL_DESCRIPTION)
                            .build(),
                    "steps",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of proof steps")
                            .build(),
                    "assertClosed",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("report an error if the target cannot be closed")
                            .build(),
                    "proof",
                    JsonSchema.builder().withType("string")
                            .withDescription("proof identifier from list_proofs; defaults to the"
                                + " selected proof")
                            .build()),
                true,
                args -> ProofScriptRunner.run(args, "tryclose",
                    List.of(tryCloseCommand(AgentTool.stringArg(args, "goal"),
                        AgentTool.intArg(args, "steps"),
                        AgentTool.boolArg(args, "assertClosed"))))),
            AgentTool.tool(KeYAgentTools.TOOL_AUTO, ToolCategory.PROOF,
                "Applies KeY's automatic proof strategy (the 'Auto' button / the 'auto'"
                    + " proof-script command) to the targeted goals, with an arbitrary maximum"
                    + " number of proof steps. Use it to try to discharge the current goal by"
                    + " automatic proof search. Proof search may take a while; this tool can run"
                    + " in the background, so you can keep asking questions while it works.",
                AgentTool.schema("goal",
                    JsonSchema.builder().withType("string").withDescription(GOAL_DESCRIPTION)
                            .build(),
                    "steps",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of proof steps (the configured"
                                + " strategy limit applies if omitted)")
                            .build(),
                    "proof",
                    JsonSchema.builder().withType("string")
                            .withDescription("proof identifier from list_proofs; defaults to the"
                                + " selected proof")
                            .build()),
                true,
                args -> {
                    var steps = AgentTool.intArg(args, "steps");
                    var command = switch (ProofScriptRunner.parseGoal(
                        AgentTool.stringArg(args, "goal"))) {
                        case ProofScriptRunner.All a ->
                            List.of(autoCommand(steps, true));
                        case ProofScriptRunner.Index idx ->
                            List.of(ProofScriptRunner.selectGoal(idx.number()),
                                autoCommand(steps, false));
                        default -> List.of(autoCommand(steps, false));
                    };
                    return ProofScriptRunner.run(args, "auto", command);
                }));
    }

    /**
     * Builds the {@code tryclose} script command from the tool parameters. {@code null}/{@code
     * blank}/{@code "branch"} targets the first open goal, {@code "all"} all open goals, and a
     * decimal string the goal with that index.
     */
    public static ScriptCommandAst tryCloseCommand(@Nullable String goal,
            @Nullable Integer steps, boolean assertClosed) {
        List<Object> positional;
        if (goal == null || goal.isBlank() || "branch".equals(goal)) {
            positional = List.of("branch");
        } else if ("all".equals(goal)) {
            positional = List.of();
        } else {
            try {
                Integer.parseInt(goal);
                positional = List.of(goal);
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException(
                    "'goal' must be \"branch\", \"all\" or a goal index, got: " + goal);
            }
        }

        var named = new HashMap<String, Object>();
        if (steps != null) {
            named.put("steps", steps);
        }
        if (assertClosed) {
            named.put("assertClosed", true);
        }
        return new ScriptCommandAst("tryclose", named, positional);
    }

    /**
     * Builds the {@code auto} script command from the tool parameters.
     */
    public static ScriptCommandAst autoCommand(@Nullable Integer steps, boolean all) {
        var named = new HashMap<String, Object>();
        if (steps != null) {
            named.put("steps", steps);
        }
        if (all) {
            named.put("all", true);
        }
        return new ScriptCommandAst("auto", named, List.of());
    }
}
