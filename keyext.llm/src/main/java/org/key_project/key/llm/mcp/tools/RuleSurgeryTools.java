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
 * The fine-grained rule-application tools {@code apply_rule}, {@code instantiate_quantifier},
 * {@code witness_constant}, {@code cut_formula}, {@code expand_definitions} and
 * {@code rewrite_term}: they wrap the corresponding KeY proof-script commands ({@code rule},
 * {@code instantiate}, {@code witness}, {@code cut}, {@code expand}, {@code rewrite}) and run
 * them through the same machinery as the "Apply Script" action, see {@link ProofScriptRunner}.
 * <p>
 * Unlike the automation tools ({@link ProofScriptTools}) all six act on a SINGLE goal: the
 * {@code goal} parameter accepts {@code "branch"} (the default - the first open goal) or an
 * open-goal index, but not {@code "all"}. The optional {@code proof} identifier from
 * {@code list_proofs} addresses another open proof; omitting it targets the selected proof.
 * <p>
 * All six mutate the proof, so they require user approval (ASK) and cannot run in the
 * background.
 *
 * @author Alexander Weigl
 */
public final class RuleSurgeryTools implements AgentToolProvider {

    /** The {@code apply_rule} tool: applies a named rule/taclet to a single goal. */
    public static final String TOOL_APPLY_RULE = "apply_rule";
    /** The {@code instantiate_quantifier} tool: instantiates a quantified formula. */
    public static final String TOOL_INSTANTIATE_QUANTIFIER = "instantiate_quantifier";
    /** The {@code witness_constant} tool: introduces a Skolem witness constant. */
    public static final String TOOL_WITNESS_CONSTANT = "witness_constant";
    /** The {@code cut_formula} tool: splits a goal on a formula. */
    public static final String TOOL_CUT_FORMULA = "cut_formula";
    /** The {@code expand_definitions} tool: unfolds definition/invariant axioms. */
    public static final String TOOL_EXPAND_DEFINITIONS = "expand_definitions";
    /** The {@code rewrite_term} tool: applies a rewrite taclet find -> replace. */
    public static final String TOOL_REWRITE_TERM = "rewrite_term";

    /** The description of the optional {@code proof} parameter shared by all six tools. */
    private static final String PROOF_DESCRIPTION =
        "proof identifier from list_proofs; defaults to the selected proof";

    @Override
    public List<AgentTool> get() {
        return List.of(
            applyRule(),
            instantiateQuantifier(),
            witnessConstant(),
            cutFormula(),
            expandDefinitions(),
            rewriteTerm());
    }

    // ------------------------------------------------------------------ the six tools

    private static AgentTool applyRule() {
        return AgentTool.tool(TOOL_APPLY_RULE, ToolCategory.PROOF,
            "applies a single named taclet or built-in rule to the sequent of one goal, using"
                + " the `rule` proof-script command. The rule is chosen by name (see"
                + " list_taclets); an optional term pattern (`on`), a top-level formula pattern,"
                + " an occurrence or schema-variable instantiations narrow where the rule"
                + " applies.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("taclet"),
                "taclet",
                stringParameter("the name of a taclet or built-in rule (see list_taclets)"),
                "on",
                stringParameter("a term pattern, with optional placeholders, where the rule's"
                    + " find-part should match"),
                "formula",
                stringParameter("a top-level formula pattern in which to apply"),
                "occ",
                JsonSchema.builder().withType("integer")
                        .withDescription("occurrence of the find-term (0-based)").build(),
                "instantiations",
                JsonSchema.builder().withType("object")
                        .withDescription("schema-variable instantiations as {name: term} string"
                            + " values")
                        .build(),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                String err = rejectAll(args, TOOL_APPLY_RULE);
                if (err == null) {
                    var taclet = AgentTool.stringArg(args, "taclet");
                    if (taclet == null || taclet.isBlank()) {
                        err = "Error: 'taclet' parameter is required";
                    } else {
                        Object inst = args.get("instantiations");
                        if (inst != null && !(inst instanceof Map<?, ?>)) {
                            err = "Error: 'instantiations' must be an object mapping"
                                + " schema-variable names to terms";
                        } else {
                            return ProofScriptRunner.run(args, TOOL_APPLY_RULE,
                                singleGoalCommand(args, ruleCommand(args, taclet, inst)));
                        }
                    }
                }
                return err;
            });
    }

    private static AgentTool instantiateQuantifier() {
        return AgentTool.tool(TOOL_INSTANTIATE_QUANTIFIER, ToolCategory.PROOF,
            "instantiates a universally or existentially quantified formula of a single goal by"
                + " substituting the term `with` for its bound variable, using the 'instantiate'"
                + " proof-script command.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("with"),
                "formula",
                stringParameter("pattern of the toplevel quantified formula; placeholder symbols"
                    + " allowed"),
                "var",
                stringParameter("the name of the bound variable to instantiate"),
                "with",
                stringParameter("the term to instantiate the bound variable with"),
                "occ",
                JsonSchema.builder().withType("integer")
                        .withDescription("occurrence number of the quantifier, starting at 1;"
                            + " default 1")
                        .build(),
                "hide",
                JsonSchema.builder().withType("boolean")
                        .withDescription("hide the instantiated formula after the step").build(),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                String err = rejectAll(args, TOOL_INSTANTIATE_QUANTIFIER);
                if (err == null) {
                    var with = AgentTool.stringArg(args, "with");
                    if (with == null || with.isBlank()) {
                        err = "Error: 'with' parameter is required";
                    } else {
                        return ProofScriptRunner.run(args, TOOL_INSTANTIATE_QUANTIFIER,
                            singleGoalCommand(args, instantiateCommand(args, with)));
                    }
                }
                return err;
            });
    }

    private static AgentTool witnessConstant() {
        return AgentTool.tool(TOOL_WITNESS_CONSTANT, ToolCategory.PROOF,
            "introduces a fresh Skolem witness constant for a quantified formula of a single"
                + " goal, using the `witness` proof-script command.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("formula", "as"),
                "formula",
                stringParameter("the quantified formula, with placeholders, for which a witness"
                    + " constant is introduced"),
                "as",
                stringParameter("the name of the fresh witness constant"),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                String err = rejectAll(args, TOOL_WITNESS_CONSTANT);
                if (err == null) {
                    var formula = AgentTool.stringArg(args, "formula");
                    var as = AgentTool.stringArg(args, "as");
                    if (formula == null || formula.isBlank()) {
                        err = "Error: 'formula' parameter is required";
                    } else if (as == null || as.isBlank()) {
                        err = "Error: 'as' parameter is required";
                    } else {
                        return ProofScriptRunner.run(args, TOOL_WITNESS_CONSTANT,
                            singleGoalCommand(args,
                                new ScriptCommandAst("witness", Map.of("as", as),
                                    List.of(formula))));
                    }
                }
                return err;
            });
    }

    private static AgentTool cutFormula() {
        return AgentTool.tool(TOOL_CUT_FORMULA, ToolCategory.PROOF,
            "cuts on a formula, splitting a single goal into the case where the formula holds and"
                + " the case where its negation holds, using the `cut` proof-script command.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("formula"),
                "formula",
                stringParameter("the formula to cut, in KeY syntax"),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                String err = rejectAll(args, TOOL_CUT_FORMULA);
                if (err == null) {
                    var formula = AgentTool.stringArg(args, "formula");
                    if (formula == null || formula.isBlank()) {
                        err = "Error: 'formula' parameter is required";
                    } else {
                        return ProofScriptRunner.run(args, TOOL_CUT_FORMULA,
                            singleGoalCommand(args,
                                new ScriptCommandAst("cut", Map.of(), List.of(formula))));
                    }
                }
                return err;
            });
    }

    private static AgentTool expandDefinitions() {
        return AgentTool.tool(TOOL_EXPAND_DEFINITIONS, ToolCategory.PROOF,
            "unfolds method-definition and class-invariant axioms of a single goal at a term or"
                + " within a top-level formula, using the `expand` proof-script command.",
            Tool.ApprovalRequirement.ASK,
            schema(null,
                "target",
                stringParameter("a term pattern matching the expansion location, e.g. a method"
                    + " name"),
                "formula",
                stringParameter("a top-level formula pattern in which to expand"),
                "occ",
                JsonSchema.builder().withType("integer")
                        .withDescription("occurrence when multiple matches exist (starts at 0)")
                        .build(),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                String err = rejectAll(args, TOOL_EXPAND_DEFINITIONS);
                if (err == null) {
                    var target = AgentTool.stringArg(args, "target");
                    var formula = AgentTool.stringArg(args, "formula");
                    if ((target == null || target.isBlank())
                            && (formula == null || formula.isBlank())) {
                        err = "Error: " + TOOL_EXPAND_DEFINITIONS
                            + " needs one of 'target' or 'formula'";
                    } else {
                        return ProofScriptRunner.run(args, TOOL_EXPAND_DEFINITIONS,
                            singleGoalCommand(args, expandCommand(args)));
                    }
                }
                return err;
            });
    }

    private static AgentTool rewriteTerm() {
        return AgentTool.tool(TOOL_REWRITE_TERM, ToolCategory.PROOF,
            "finds and applies a rewrite taclet that turns the given `find` term into the"
                + " `replace` term on a single goal, using the `rewrite` proof-script command;"
                + " falls back to a cut when no matching rewrite taclet exists.",
            Tool.ApprovalRequirement.ASK,
            schema(List.of("find", "replace"),
                "find",
                stringParameter("the term to rewrite"),
                "replace",
                stringParameter("the replacement term"),
                "formula",
                stringParameter("restrict to a top-level formula"),
                "goal", goalParameter(),
                "proof", proofParameter()),
            false,
            args -> {
                String err = rejectAll(args, TOOL_REWRITE_TERM);
                if (err == null) {
                    var find = AgentTool.stringArg(args, "find");
                    var replace = AgentTool.stringArg(args, "replace");
                    if (find == null || find.isBlank()) {
                        err = "Error: 'find' parameter is required";
                    } else if (replace == null || replace.isBlank()) {
                        err = "Error: 'replace' parameter is required";
                    } else {
                        var named = new HashMap<String, Object>();
                        named.put("find", find);
                        named.put("replace", replace);
                        var formula = AgentTool.stringArg(args, "formula");
                        if (formula != null) {
                            named.put("formula", formula);
                        }
                        return ProofScriptRunner.run(args, TOOL_REWRITE_TERM,
                            singleGoalCommand(args, new ScriptCommandAst("rewrite", named,
                                List.of())));
                    }
                }
                return err;
            });
    }

    // ------------------------------------------------------------------ script command builders

    /**
     * Builds the {@code rule} script command: the positional rule name plus the optional
     * {@code on}/{@code formula}/{@code occ} parameters and the {@code inst_*} schema-variable
     * instantiations.
     */
    private static ScriptCommandAst ruleCommand(Map<String, Object> args, String taclet,
            @Nullable Object inst) {
        var named = new HashMap<String, Object>();
        var on = AgentTool.stringArg(args, "on");
        if (on != null) {
            named.put("on", on);
        }
        var formula = AgentTool.stringArg(args, "formula");
        if (formula != null) {
            named.put("formula", formula);
        }
        var occ = AgentTool.intArg(args, "occ");
        if (occ != null) {
            named.put("occ", occ);
        }
        if (inst instanceof Map<?, ?> instantiations) {
            for (var entry : instantiations.entrySet()) {
                named.put("inst_" + entry.getKey(), String.valueOf(entry.getValue()));
            }
        }
        return new ScriptCommandAst("rule", named, List.of(taclet));
    }

    /**
     * Builds the {@code instantiate} script command from the tool parameters; {@code with} (the
     * instantiation term) is required and always present.
     */
    private static ScriptCommandAst instantiateCommand(Map<String, Object> args, String with) {
        var named = new HashMap<String, Object>();
        var formula = AgentTool.stringArg(args, "formula");
        if (formula != null) {
            named.put("formula", formula);
        }
        var boundVar = AgentTool.stringArg(args, "var");
        if (boundVar != null) {
            named.put("var", boundVar);
        }
        named.put("with", with);
        var occ = AgentTool.intArg(args, "occ");
        if (occ != null) {
            named.put("occ", occ);
        }
        if (AgentTool.boolArg(args, "hide")) {
            named.put("hide", true);
        }
        return new ScriptCommandAst("instantiate", named, List.of());
    }

    /**
     * Builds the {@code expand} script command: the expansion location as {@code on} (from
     * {@code target}) with a fallback to {@code formula}, plus the optional {@code occ}.
     */
    private static ScriptCommandAst expandCommand(Map<String, Object> args) {
        var named = new HashMap<String, Object>();
        var target = AgentTool.stringArg(args, "target");
        var formula = AgentTool.stringArg(args, "formula");
        if (target != null) {
            named.put("on", target);
        } else {
            named.put("formula", formula);
        }
        var occ = AgentTool.intArg(args, "occ");
        if (occ != null) {
            named.put("occ", occ);
        }
        return new ScriptCommandAst("expand", named, List.of());
    }

    // ------------------------------------------------------------------ shared goal handling

    /**
     * Rejects the {@code "all"} goal target - the surgery tools act on a single goal. Returns
     * the error message to surface, or {@code null} when the goal targets a single goal.
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
    private static JsonSchema schema(@Nullable List<String> required, Object... keyValue) {
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

    private static JsonSchema goalParameter() {
        return stringParameter(ProofScriptTools.GOAL_DESCRIPTION);
    }

    private static JsonSchema proofParameter() {
        return stringParameter(PROOF_DESCRIPTION);
    }
}
