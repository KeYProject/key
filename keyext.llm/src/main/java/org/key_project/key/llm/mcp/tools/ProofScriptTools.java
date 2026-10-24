/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.scripts.ScriptException;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.ToolCategory;

import org.jspecify.annotations.Nullable;

/**
 * The proof-manipulation tools {@code tryclose} and {@code auto}: they execute the corresponding
 * KeY proof-script commands on the selected proof through the same machinery as the "Apply
 * Script" action.
 *
 * @author Alexander Weigl
 */
public final class ProofScriptTools implements AgentToolProvider {
    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_TRYCLOSE, ToolCategory.PROOF,
                "Applies the KeY proof-script command 'tryclose' to the current proof: it"
                    + " automatically tries to close goals with the TryClose strategy. Targets"
                    + " either the first open goal of the current branch (default), all open"
                    + " goals, or a single goal by index.",
                AgentTool.schema("branch",
                    JsonSchema.builder().withType("string")
                            .withDescription("the target: \"branch\" (first open goal, default),"
                                + " \"all\" (all open goals), or the 0-based index of one open"
                                + " goal")
                            .build(),
                    "steps",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of proof steps")
                            .build(),
                    "assertClosed",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("report an error if the target cannot be closed")
                            .build()),
                args -> runScript(tryCloseCommand(AgentTool.stringArg(args, "branch"),
                    AgentTool.intArg(args, "steps"), AgentTool.boolArg(args, "assertClosed")))),
            AgentTool.tool(KeYAgentTools.TOOL_AUTO, ToolCategory.PROOF,
                "Applies KeY's automatic proof strategy (the 'Auto' button / the 'auto'"
                    + " proof-script command) to the current branch, with an arbitrary maximum"
                    + " number of proof steps. Use it to try to discharge the current goal by"
                    + " automatic proof search. Proof search may take a while; this tool can run"
                    + " in the background, so you can keep asking questions while it works.",
                AgentTool.schema("steps",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of proof steps (the configured"
                                + " strategy limit applies if omitted)")
                            .build(),
                    "all",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("apply the strategy to all open goals instead of the"
                                + " first one")
                            .build()),
                true,
                args -> runScript(autoCommand(AgentTool.intArg(args, "steps"),
                    AgentTool.boolArg(args, "all")))));
    }

    /**
     * Builds the {@code tryclose} script command from the tool parameters. {@code null}/{@code
     * blank}/{@code "branch"} targets the first open goal, {@code "all"} all open goals, and a
     * decimal string the goal with that index.
     */
    public static ScriptCommandAst tryCloseCommand(@Nullable String branch,
            @Nullable Integer steps, boolean assertClosed) {
        List<Object> positional;
        if (branch == null || branch.isBlank() || "branch".equals(branch)) {
            positional = List.of("branch");
        } else if ("all".equals(branch)) {
            positional = List.of();
        } else {
            try {
                Integer.parseInt(branch);
                positional = List.of(branch);
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException(
                    "'branch' must be \"branch\", \"all\" or a goal index, got: " + branch);
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

    /**
     * Executes a single proof-script command on the currently selected proof via the
     * {@link ProofScriptEngine}, i.e. through the same machinery as the "Apply Script" action.
     * The result tells the agent how many open goals remain.
     */
    private static String runScript(ScriptCommandAst command) {
        var proof = ProofSelector.selectedProof();
        if (proof == null) {
            return "Error: no proof selected";
        }
        int before = proof.openGoals().size();
        var ui = MainWindow.getInstance().getMediator().getUI();
        try {
            new ProofScriptEngine(proof).execute(ui, List.of(command));
        } catch (ScriptException e) {
            return "Error: " + e.getMessage();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return "Error: proof search interrupted";
        }
        int after = proof.openGoals().size();
        int closed = before - after;
        return command.commandName() + ": " + closed + " goal(s) closed, " + after
            + " open goal(s) remain" + (after == 0 ? " - the proof is closed" : "") + ".";
    }
}
