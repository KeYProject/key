/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.jspecify.annotations.Nullable;

/**
 * The sequent-editing tools {@code hide_sequent}, {@code unhide_sequent}, {@code focus_goal} and
 * {@code let_abbrev}: they wrap the corresponding KeY proof-script commands ({@code hide},
 * {@code unhide}, {@code focus}, {@code let}/{@code letf}) and run them through the same
 * machinery as the "Apply Script" action, see {@link ProofScriptRunner}.
 * <p>
 * The first three manipulate the formula visibility of a SINGLE goal - hiding every formula that
 * matches a sequent pattern ({@code hide}), re-inserting previously hidden ones ({@code unhide})
 * or keeping only the formulas of a pattern and hiding the rest ({@code focus}) - to declutter
 * the sequent for the strategy and the model. Their {@code goal} parameter accepts
 * {@code "branch"} (the default - the first open goal) or an open-goal index, but not
 * {@code "all"}. {@code let_abbrev} is proof-wide: it introduces or updates a term abbreviation
 * in the proof's abbreviation map (used when pretty-printing and parsing the proof) and has no
 * {@code goal} parameter.
 * <p>
 * All four mutate the proof, so they require user approval (ASK) and cannot run in the
 * background. The optional {@code proof} identifier from {@code list_proofs} addresses another
 * open proof; omitting it targets the selected proof.
 *
 * @author Alexander Weigl
 */
public final class SequentEditingTools implements AgentToolProvider {

    /** The {@code hide_sequent} tool: hides the formulas of one goal matching a sequent pattern. */
    public static final String TOOL_HIDE_SEQUENT = "hide_sequent";
    /** The {@code unhide_sequent} tool: re-inserts previously hidden formulas of one goal. */
    public static final String TOOL_UNHIDE_SEQUENT = "unhide_sequent";
    /** The {@code focus_goal} tool: keeps only the given formulas of one goal. */
    public static final String TOOL_FOCUS_GOAL = "focus_goal";
    /** The {@code let_abbrev} tool: introduces or updates a term abbreviation. */
    public static final String TOOL_LET_ABBREV = "let_abbrev";

    /** The description of the optional {@code proof} parameter shared by all four tools. */
    private static final String PROOF_DESCRIPTION =
        "proof identifier from list_proofs; defaults to the selected proof";

    @Override
    public List<AgentTool> get() {
        return List.of(
            hideSequent(),
            unhideSequent(),
            focusGoal(),
            letAbbrev());
    }

    // ------------------------------------------------------------------ the four tools

    private static AgentTool hideSequent() {
        return AgentTool.tool(TOOL_HIDE_SEQUENT, ToolCategory.PROOF,
            "hides all formulas of one goal that match the given sequent pattern - the `hide`"
                + " proof-script command: each matching formula is removed from view (via"
                + " hide_left/hide_right) and can be restored later with `unhide_sequent`. Use it"
                + " to declutter the sequent for the strategy and the model.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("sequent"),
                "sequent",
                stringParameter("a sequent pattern of the formulas to hide, e.g. `x > 0 ==>`;"
                    + " placeholders allowed"),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                var sequent = AgentTool.stringArg(args, "sequent");
                if (sequent == null || sequent.isBlank()) {
                    return "Error: 'sequent' parameter is required";
                }
                String err = rejectAll(args, TOOL_HIDE_SEQUENT);
                if (err == null) {
                    return ProofScriptRunner.run(args, TOOL_HIDE_SEQUENT,
                        singleGoalCommand(args,
                            new ScriptCommandAst("hide", Map.of(), List.of(sequent))));
                }
                return err;
            });
    }

    private static AgentTool unhideSequent() {
        return AgentTool.tool(TOOL_UNHIDE_SEQUENT, ToolCategory.PROOF,
            "re-inserts the formulas of one goal that match the given sequent pattern and were"
                + " hidden earlier - the `unhide` proof-script command: every hidden formula"
                + " matching the pattern is shown again on the sequent.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("sequent"),
                "sequent",
                stringParameter("a sequent pattern of the formulas to re-insert, e.g. `x > 0`;"
                    + " placeholders allowed"),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                var sequent = AgentTool.stringArg(args, "sequent");
                if (sequent == null || sequent.isBlank()) {
                    return "Error: 'sequent' parameter is required";
                }
                String err = rejectAll(args, TOOL_UNHIDE_SEQUENT);
                if (err == null) {
                    return ProofScriptRunner.run(args, TOOL_UNHIDE_SEQUENT,
                        singleGoalCommand(args,
                            new ScriptCommandAst("unhide", Map.of(), List.of(sequent))));
                }
                return err;
            });
    }

    private static AgentTool focusGoal() {
        return AgentTool.tool(TOOL_FOCUS_GOAL, ToolCategory.PROOF,
            "keeps only the formulas of one goal that match the given sequent pattern - the"
                + " `focus` proof-script command: every other formula of the goal is hidden,"
                + " guiding the automation (and the model) toward the relevant formulas.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("keep"),
                "keep",
                stringParameter("a sequent pattern of the formulas to keep; every other formula"
                    + " of the goal is hidden, e.g. `x > 1 ==> y = x`"),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                var keep = AgentTool.stringArg(args, "keep");
                if (keep == null || keep.isBlank()) {
                    return "Error: 'keep' parameter is required";
                }
                String err = rejectAll(args, TOOL_FOCUS_GOAL);
                if (err == null) {
                    return ProofScriptRunner.run(args, TOOL_FOCUS_GOAL,
                        singleGoalCommand(args,
                            new ScriptCommandAst("focus", Map.of(), List.of(keep))));
                }
                return err;
            });
    }

    private static AgentTool letAbbrev() {
        return AgentTool.tool(TOOL_LET_ABBREV, ToolCategory.PROOF,
            "introduces or updates a term abbreviation used when pretty-printing and parsing the"
                + " proof - the `let`/`letf` proof-script commands: `name` abbreviates `term` in"
                + " the proof's abbreviation map. Redefining an existing abbreviation fails"
                + " unless `force` overrides it (the `letf` variant).",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("name", "term"),
                "name",
                stringParameter("the abbreviation name without the leading @"),
                "term",
                stringParameter("the term the abbreviation stands for, in KeY syntax"),
                "force",
                booleanParameter("overwrite an existing abbreviation with the same name instead"
                    + " of failing (the `letf` variant)"),
                "proof", proofParameter()),
            false,
            args -> {
                var name = AgentTool.stringArg(args, "name");
                var term = AgentTool.stringArg(args, "term");
                var named = new HashMap<String, Object>();
                if (name != null && !name.isBlank() && term != null && !term.isBlank()) {
                    named.put("@" + name, term);
                }
                var command = new ScriptCommandAst(
                    AgentTool.boolArg(args, "force") ? "letf" : "let", named, List.of());
                return ProofScriptRunner.run(args, TOOL_LET_ABBREV, List.of(command));
            });
    }

    // ------------------------------------------------------------------ shared goal handling

    /**
     * Rejects the {@code "all"} goal target - the sequent-editing tools act on a single goal.
     * Returns the error message to surface, or {@code null} when the target is a single goal.
     */
    private static @Nullable String rejectAll(Map<String, Object> args, String tool) {
        return "all".equals(AgentTool.stringArg(args, "goal"))
            ? "Error: " + tool + " acts on a single goal: use \"branch\" or an index, not"
                + " \"all\"."
            : null;
    }

    /**
     * Builds the goal-targeted command list: the command itself for the default branch target,
     * prefixed with a {@code select} for an open-goal index. The {@code "all"} target must
     * already be rejected by {@link #rejectAll}.
     */
    private static List<ScriptCommandAst> singleGoalCommand(Map<String, Object> args,
            ScriptCommandAst command) {
        return switch (ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal"))) {
            case ProofScriptRunner.Index idx ->
                List.of(ProofScriptRunner.selectGoal(idx.number()), command);
            default -> List.of(command);
        };
    }

    // ------------------------------------------------------------------ schema helpers

    /** Builds an object schema from alternating key/value pairs with the given required names. */
    private static JsonSchema schema(List<String> required, Object... keyValue) {
        var builder = JsonSchema.builder().withType("object");
        for (int i = 0; i + 1 < keyValue.length; i += 2) {
            builder.addProperty((String) keyValue[i], (JsonSchema) keyValue[i + 1]);
        }
        if (required != null && !required.isEmpty()) {
            builder.withRequired(required);
        }
        return builder.build();
    }

    private static JsonSchema stringParameter(String description) {
        return JsonSchema.builder().withType("string").withDescription(description).build();
    }

    private static JsonSchema booleanParameter(String description) {
        return JsonSchema.builder().withType("boolean").withDescription(description).build();
    }

    private static JsonSchema goalParameter() {
        return stringParameter(ProofScriptTools.GOAL_DESCRIPTION);
    }

    private static JsonSchema proofParameter() {
        return stringParameter(PROOF_DESCRIPTION);
    }
}
