/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.jspecify.annotations.Nullable;

/**
 * The {@code run_script} tool: a strategy runner that executes a short, user-visible sequence of
 * guarded proof-script steps (at most {@value #MAX_STEPS}) on the targeted goals.
 * <p>
 * Only the already-exposed proof-script commands are whitelisted ({@code tryclose}, {@code auto},
 * {@code macro}, {@code smt}, {@code oss}, {@code apply_rule}, {@code instantiate_quantifier},
 * {@code witness_constant}, {@code cut_formula}, {@code expand_definitions} and
 * {@code rewrite_term}); everything else - in particular free-form scripts and the unguarded
 * {@code assume}, {@code axiom} and {@code cheat} commands - is rejected with an error naming the
 * offending step. The whole sequence is validated before anything runs: every step must be an
 * object with a known {@code command}, its {@code args} may only contain the parameters of that
 * command, and the sequence is bounded to at most {@value #MAX_STEPS} steps.
 * <p>
 * A step targets the first open goal of the current branch by default or a single goal by its
 * open-goal index; the selection is translated into {@code select} prefixes
 * ({@link ProofScriptRunner#selectGoal(int)}) and persists across the following steps, so a
 * multi-step strategy can continue on the goal it just produced. Like the surgery tools
 * ({@link RuleSurgeryTools}) this mutates the proof and therefore requires user approval and
 * cannot run in the background.
 *
 * @author Alexander Weigl
 */
public final class ScriptSequenceTools implements AgentToolProvider {
    /** The {@code run_script} tool. */
    public static final String TOOL_RUN_SCRIPT = "run_script";

    /** The hard bound on the number of steps a single call accepts. */
    private static final int MAX_STEPS = 8;

    /** The whitelisted step commands, in schema/enum and error-message order. */
    private static final List<String> COMMANDS = List.of("tryclose", "auto", "macro", "smt", "oss",
        "apply_rule", "instantiate_quantifier", "witness_constant", "cut_formula",
        "expand_definitions", "rewrite_term");

    /** The same commands as a set, for validating the step's {@code command}. */
    private static final Set<String> COMMAND_SET = Set.copyOf(COMMANDS);

    /** The curated macros the {@code macro} step may run, in schema/enum order. */
    private static final List<String> MACRO_OPTIONS = List.of("symbex", "symbex-only", "onestep",
        "tryclose-sidebranches", "split-prop", "nosplit-prop", "simp-int", "simp-heap", "simp-upd",
        "transcendental", "autopilot");

    /** The same macros as a set, for validating the {@code macro} argument. */
    private static final Set<String> MACROS = Set.copyOf(MACRO_OPTIONS);

    /**
     * The parameters each whitelisted step command accepts inside its {@code args} (the
     * per-command {@code goal} key is listed for uniformity but is read from the step object).
     */
    private static final Map<String, List<String>> ALLOWED_KEYS = Map.ofEntries(
        Map.entry("tryclose", List.of("goal", "steps", "assertClosed")),
        Map.entry("auto", List.of("goal", "steps")),
        Map.entry("macro", List.of("goal", "macro")),
        Map.entry("smt", List.of("goal", "solver", "timeout")),
        Map.entry("oss", List.of("goal", "antecedent", "succedent", "recent_only")),
        Map.entry("apply_rule", List.of("goal", "taclet", "on", "formula", "occ", "instantiations")),
        Map.entry("instantiate_quantifier", List.of("goal", "formula", "var", "with", "occ", "hide")),
        Map.entry("witness_constant", List.of("goal", "formula", "as")),
        Map.entry("cut_formula", List.of("goal", "formula")),
        Map.entry("expand_definitions", List.of("goal", "target", "formula", "occ")),
        Map.entry("rewrite_term", List.of("goal", "find", "replace", "formula")));

    @Override
    public List<AgentTool> get() {
        return List.of(AgentTool.tool(TOOL_RUN_SCRIPT, ToolCategory.PROOF,
            "runs a short sequence (at most " + MAX_STEPS + " steps) of guarded proof-script"
                + " steps on the targeted goals - a strategy runner over the whitelisted commands"
                + " tryclose, auto, macro, smt, oss, apply_rule, instantiate_quantifier,"
                + " witness_constant, cut_formula, expand_definitions and rewrite_term. A step"
                + " targets the first open goal of the current branch by default or a single goal"
                + " by its open-goal index, and the selection persists across the following"
                + " steps. Only the listed commands are accepted; free-form scripts and the"
                + " unguarded assume/axiom/cheat commands are rejected, and every step is"
                + " validated before anything runs.",
            Tool.ApprovalRequirement.ASK,
            schema(),
            false,
            args -> {
                Object raw = args.get("steps");
                if (!(raw instanceof List<?> steps)) {
                    return "Error: 'steps' must be an array of step objects, got: " + raw;
                }
                if (steps.isEmpty()) {
                    return "Error: 'steps' must not be empty";
                }
                if (steps.size() > MAX_STEPS) {
                    return "Error: run_script accepts at most " + MAX_STEPS + " steps";
                }
                List<ScriptCommandAst> commands = new ArrayList<>();
                for (int i = 0; i < steps.size(); i++) {
                    Object element = steps.get(i);
                    if (!(element instanceof Map<?, ?> step)) {
                        return "Error: run_script step " + i + ": expected a step object";
                    }
                    String err = parseStep(i, step, commands);
                    if (err != null) {
                        return err;
                    }
                }
                return ProofScriptRunner.run(args, "run_script", commands);
            }));
    }

    // ------------------------------------------------------------------ schema

    private static JsonSchema schema() {
        JsonSchema items = JsonSchema.builder().withType("object")
            .addProperty("command",
                JsonSchema.builder().withType("string")
                        .withDescription("the proof-script command to run; one of the"
                            + " whitelisted commands (tryclose, auto, macro, smt, oss,"
                            + " apply_rule, instantiate_quantifier, witness_constant,"
                            + " cut_formula, expand_definitions, rewrite_term)")
                        .withEnum(COMMANDS)
                        .build())
            .addProperty("args",
                JsonSchema.builder().withType("object")
                        .withDescription("the parameters of the command; only the whitelisted"
                            + " parameters of the chosen command are accepted, e.g. steps for"
                            + " tryclose/auto, macro for macro, taclet/on/formula/occ/"
                            + " instantiations for apply_rule, find/replace/formula for"
                            + " rewrite_term")
                        .build())
            .addProperty("goal",
                JsonSchema.builder().withType("string")
                        .withDescription(ProofScriptTools.GOAL_DESCRIPTION)
                        .build())
            .addRequired("command")
            .build();
        return JsonSchema.builder().withType("object")
            .addProperty("steps",
                JsonSchema.builder().withType("array")
                        .withDescription("the sequence of proof-script steps to run, at most "
                            + MAX_STEPS)
                        .withItems(items)
                        .build())
            .addProperty("proof",
                JsonSchema.builder().withType("string")
                        .withDescription("proof identifier from list_proofs; defaults to the"
                            + " selected proof")
                        .build())
            .addRequired("steps")
            .build();
    }

    // ------------------------------------------------------------------ step validation

    /**
     * Validates one step of the sequence and appends its (possibly {@code select}-prefixed) script
     * command to {@code out}. Returns an error message (0-based step numbers), or {@code null}
     * when the step is accepted.
     */
    private static @Nullable String parseStep(int i, Map<?, ?> step, List<ScriptCommandAst> out) {
        Object rawCommand = step.get("command");
        String command = rawCommand == null ? null : String.valueOf(rawCommand);
        if (command == null || command.isBlank() || !COMMAND_SET.contains(command)) {
            return "Error: run_script step " + i + ": unknown command '" + rawCommand
                + "'; allowed: " + String.join(", ", COMMANDS);
        }

        Map<?, ?> stepArgs;
        Object a = step.get("args");
        if (a == null) {
            stepArgs = Map.of();
        } else if (a instanceof Map<?, ?> map) {
            stepArgs = map;
        } else {
            return "Error: run_script step " + i + " (" + command + "): 'args' must be an"
                + " object";
        }
        List<String> allowed = ALLOWED_KEYS.get(command);
        for (Object keyObject : stepArgs.keySet()) {
            String key = String.valueOf(keyObject);
            if (!allowed.contains(key)) {
                return "Error: run_script step " + i + " (" + command + "): unknown parameter '"
                    + key + "'; allowed: " + String.join(", ", allowed);
            }
        }

        Object goal = step.get("goal");
        if ("all".equals(goal == null ? null : String.valueOf(goal))) {
            return "Error: run_script step " + i + " (" + command
                + "): \"all\" is not supported inside run_script; use \"branch\" or an index";
        }
        String index = indexString(goal);
        if (index != null) {
            out.add(ProofScriptRunner.selectGoal(Integer.parseInt(index)));
        }
        return addCommand(i, command, stepArgs, goal, out);
    }

    /**
     * Builds the script command AST for one whitelisted step from its validated {@code args} and
     * appends it to {@code out}; the per-command parameter errors are reported with the step
     * prefix and the step's command name.
     */
    private static @Nullable String addCommand(int i, String command, Map<?, ?> stepArgs,
            Object goal, List<ScriptCommandAst> out) {
        switch (command) {
            case "tryclose" -> {
                var named = new HashMap<String, Object>();
                Integer steps = integer(stepArgs, "steps");
                if (steps != null) {
                    named.put("steps", steps);
                }
                if (bool(stepArgs, "assertClosed")) {
                    named.put("assertClosed", true);
                }
                String index = indexString(goal);
                List<Object> positional = index == null ? List.of("branch") : List.of(index);
                out.add(new ScriptCommandAst("tryclose", named, positional));
            }
            case "auto" -> {
                var named = new HashMap<String, Object>();
                Integer steps = integer(stepArgs, "steps");
                if (steps != null) {
                    named.put("steps", steps);
                }
                out.add(new ScriptCommandAst("auto", named, List.of()));
            }
            case "macro" -> {
                String macro = str(stepArgs, "macro");
                if (macro == null || macro.isBlank() || !MACROS.contains(macro)) {
                    return "Error: run_script step " + i + " (macro): unknown macro '" + macro
                        + "'; choose from: " + String.join(", ", MACRO_OPTIONS);
                }
                out.add(new ScriptCommandAst("macro", Map.of(), List.of(macro)));
            }
            case "smt" -> {
                var named = new HashMap<String, Object>();
                String solver = str(stepArgs, "solver");
                if (solver != null && !solver.isBlank()) {
                    named.put("solver", solver);
                }
                Integer timeout = integer(stepArgs, "timeout");
                if (timeout != null && timeout >= 0) {
                    named.put("timeout", timeout);
                }
                out.add(new ScriptCommandAst("smt", named, List.of()));
            }
            case "oss" -> {
                var named = new HashMap<String, Object>();
                if (stepArgs.containsKey("antecedent") && !bool(stepArgs, "antecedent")) {
                    named.put("antecedent", false);
                }
                if (stepArgs.containsKey("succedent") && !bool(stepArgs, "succedent")) {
                    named.put("succedent", false);
                }
                if (bool(stepArgs, "recent_only")) {
                    named.put("recentOnly", true);
                }
                out.add(new ScriptCommandAst("oss", named, List.of()));
            }
            case "apply_rule" -> {
                String taclet = str(stepArgs, "taclet");
                if (taclet == null || taclet.isBlank()) {
                    return "Error: run_script step " + i + " (apply_rule): 'taclet' is required";
                }
                var named = new HashMap<String, Object>();
                String on = str(stepArgs, "on");
                if (on != null) {
                    named.put("on", on);
                }
                String formula = str(stepArgs, "formula");
                if (formula != null) {
                    named.put("formula", formula);
                }
                Integer occ = integer(stepArgs, "occ");
                if (occ != null) {
                    named.put("occ", occ);
                }
                Object inst = stepArgs.get("instantiations");
                if (inst != null) {
                    if (!(inst instanceof Map<?, ?> instantiations)) {
                        return "Error: run_script step " + i + " (apply_rule): 'instantiations'"
                            + " must be an object mapping schema-variable names to terms";
                    }
                    for (var entry : instantiations.entrySet()) {
                        named.put("inst_" + entry.getKey(), String.valueOf(entry.getValue()));
                    }
                }
                out.add(new ScriptCommandAst("rule", named, List.of(taclet)));
            }
            case "instantiate_quantifier" -> {
                String with = str(stepArgs, "with");
                if (with == null || with.isBlank()) {
                    return "Error: run_script step " + i + " (instantiate_quantifier): 'with'"
                        + " is required";
                }
                var named = new HashMap<String, Object>();
                String formula = str(stepArgs, "formula");
                if (formula != null) {
                    named.put("formula", formula);
                }
                String var = str(stepArgs, "var");
                if (var != null) {
                    named.put("var", var);
                }
                named.put("with", with);
                Integer occ = integer(stepArgs, "occ");
                if (occ != null) {
                    named.put("occ", occ);
                }
                if (bool(stepArgs, "hide")) {
                    named.put("hide", true);
                }
                out.add(new ScriptCommandAst("instantiate", named, List.of()));
            }
            case "witness_constant" -> {
                String formula = str(stepArgs, "formula");
                if (formula == null || formula.isBlank()) {
                    return "Error: run_script step " + i + " (witness_constant): 'formula'"
                        + " parameter is required";
                }
                String as = str(stepArgs, "as");
                if (as == null || as.isBlank()) {
                    return "Error: run_script step " + i + " (witness_constant): 'as' parameter"
                        + " is required";
                }
                out.add(new ScriptCommandAst("witness", Map.of("as", as), List.of(formula)));
            }
            case "cut_formula" -> {
                String formula = str(stepArgs, "formula");
                if (formula == null || formula.isBlank()) {
                    return "Error: run_script step " + i + " (cut_formula): 'formula' parameter"
                        + " is required";
                }
                out.add(new ScriptCommandAst("cut", Map.of(), List.of(formula)));
            }
            case "expand_definitions" -> {
                String target = str(stepArgs, "target");
                String formula = str(stepArgs, "formula");
                if ((target == null || target.isBlank())
                        && (formula == null || formula.isBlank())) {
                    return "Error: run_script step " + i + " (expand_definitions): needs one of"
                        + " 'target' or 'formula'";
                }
                var named = new HashMap<String, Object>();
                if (target != null) {
                    named.put("on", target);
                } else {
                    named.put("formula", formula);
                }
                Integer occ = integer(stepArgs, "occ");
                if (occ != null) {
                    named.put("occ", occ);
                }
                out.add(new ScriptCommandAst("expand", named, List.of()));
            }
            case "rewrite_term" -> {
                String find = str(stepArgs, "find");
                if (find == null || find.isBlank()) {
                    return "Error: run_script step " + i + " (rewrite_term): 'find' parameter"
                        + " is required";
                }
                String replace = str(stepArgs, "replace");
                if (replace == null || replace.isBlank()) {
                    return "Error: run_script step " + i + " (rewrite_term): 'replace' parameter"
                        + " is required";
                }
                var named = new HashMap<String, Object>();
                named.put("find", find);
                named.put("replace", replace);
                String formula = str(stepArgs, "formula");
                if (formula != null) {
                    named.put("formula", formula);
                }
                out.add(new ScriptCommandAst("rewrite", named, List.of()));
            }
            default -> throw new IllegalStateException("unreachable: " + command);
        }
        return null;
    }

    // ------------------------------------------------------------------ argument helpers

    /** The {@code goal} value as a trimmed selectable index string, or {@code null}. */
    private static @Nullable String indexString(Object goal) {
        if (goal == null) {
            return null;
        }
        String g = String.valueOf(goal).trim();
        try {
            Integer.parseInt(g);
            return g;
        } catch (NumberFormatException e) {
            return null;
        }
    }

    /** The step argument as a string, or {@code null} when absent. */
    private static @Nullable String str(Map<?, ?> args, String key) {
        Object v = args.get(key);
        return v == null ? null : String.valueOf(v);
    }

    /** The step argument as an integer, or {@code null} when absent or not a number. */
    private static @Nullable Integer integer(Map<?, ?> args, String key) {
        Object v = args.get(key);
        if (v instanceof Number n) {
            return n.intValue();
        }
        if (v != null) {
            try {
                return Integer.parseInt(String.valueOf(v).trim());
            } catch (NumberFormatException e) {
                return null;
            }
        }
        return null;
    }

    /** The step argument as a boolean (accepts JSON booleans and the string "true"). */
    private static boolean bool(Map<?, ?> args, String key) {
        Object v = args.get(key);
        return (v instanceof Boolean b && b) || "true".equals(v);
    }
}
