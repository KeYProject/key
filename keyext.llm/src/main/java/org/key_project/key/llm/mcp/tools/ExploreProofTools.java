/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.SideProofUtil;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;
import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * The exploration tools {@code probe_add_formula}, {@code probe_edit_formula},
 * {@code explorative_add_formula} and {@code explorative_edit_formula} - a 2x2 family around the
 * two "what if" operations the KeY exploration mode offers: adding a formula to a sequent side,
 * and replacing a formula of the sequent by another one.
 * <p>
 * The {@code probe_*} tools answer "would the goal be provable if the formula were added /
 * replaced?" by running the default auto strategy on an ISOLATED SIDE PROOF built with
 * {@link SideProofUtil} (environment cloned with its own one-step simplifier, root sequent =
 * the targeted goal's sequent modified accordingly). The side proof is never registered anywhere
 * and is discarded after the run, so the main proof is untouched - "always pruned back to the
 * original goal" holds by construction. They are safe to approve automatically.
 * <p>
 * The {@code explorative_*} tools perform the same operation IN THE MAIN PROOF, following the
 * exploration-mode recipe (see the {@code ProofExplorationService} of {@code keyext.exploration},
 * reimplemented here without the dependency): the new formula is introduced by a {@code cut} rule
 * application, the old occurrence is hidden on the branch that carries the new formula (edit
 * case), and the other cut branch - the case without the new formula - is disabled (made
 * interactive). This REFRAMES the theorem around the added/replaced formula: the proof can only be
 * closed for the modified obligation (the disabled branch should be pruned before closing), which
 * is exactly the exploration semantics.
 *
 * @author Alexander Weigl
 */
public final class ExploreProofTools implements AgentToolProvider {
    /** The {@code probe_add_formula} tool. */
    public static final String TOOL_PROBE_ADD_FORMULA = "probe_add_formula";
    /** The {@code probe_edit_formula} tool. */
    public static final String TOOL_PROBE_EDIT_FORMULA = "probe_edit_formula";
    /** The {@code explorative_add_formula} tool. */
    public static final String TOOL_EXPLORATIVE_ADD_FORMULA = "explorative_add_formula";
    /** The {@code explorative_edit_formula} tool. */
    public static final String TOOL_EXPLORATIVE_EDIT_FORMULA = "explorative_edit_formula";

    /** The default rule-application budget of the auto strategy on a side proof. */
    private static final int DEFAULT_STEPS = 2000;

    /** The two sequent sides a formula can be added to / replaced on. */
    private static final List<String> SIDES = List.of("antecedent", "succedent");

    private static final String PROOF_DES =
        "proof identifier from list_proofs; defaults to the selected proof";
    private static final String SIDE_DESCRIPTION =
        "the sequent side to modify: \"antecedent\" (assumptions) or \"succedent\" (conclusions);"
            + " defaults to antecedent";

    @Override
    public List<AgentTool> get() {
        return List.of(
            probeAddFormula(),
            probeEditFormula(),
            explorativeAddFormula(),
            explorativeEditFormula());
    }

    // ------------------------------------------------------------------ the four tools

    private static AgentTool probeAddFormula() {
        return AgentTool.tool(TOOL_PROBE_ADD_FORMULA, ToolCategory.PROOF,
            "probe: run the KeY auto strategy on an isolated side proof (built with"
                + " SideProofUtil) of the targeted goal with the given formula ADDED to the"
                + " antecedent or succedent, and report whether the goal then closes under the"
                + " step/timeout budget; the main proof is never modified (the side proof is"
                + " discarded - always pruned back to the original goal).",
            JsonSchema.builder().withType("object")
                    .addProperty("formula", stringParameter(
                        "the formula to add to the side proof, in KeY syntax"))
                    .addProperty("side", sideParameter())
                    .addProperty("steps", intParameter(
                        "maximum rule applications for the auto strategy; default 2000"))
                    .addProperty("timeout", intParameter("solver-style timeout in seconds"))
                    .addProperty("goal", goalParameter())
                    .addProperty("proof", stringParameter(PROOF_DES))
                    .addRequired("formula")
                    .build(),
            true,
            args -> runProbe(args, TOOL_PROBE_ADD_FORMULA, null, null));
    }

    private static AgentTool probeEditFormula() {
        return AgentTool.tool(TOOL_PROBE_EDIT_FORMULA, ToolCategory.PROOF,
            "probe: run the KeY auto strategy on an isolated side proof (built with"
                + " SideProofUtil) of the targeted goal where the first occurrence of 'find' on"
                + " the chosen sequent side is REPLACED by 'replace', and report whether the goal"
                + " then closes under the step/timeout budget; the main proof is never modified"
                + " (the side proof is discarded - always pruned back to the original goal).",
            JsonSchema.builder().withType("object")
                    .addProperty("find", stringParameter(
                        "the formula to replace, in KeY syntax (must occur on the given side)"))
                    .addProperty("replace", stringParameter(
                        "the formula that replaces it, in KeY syntax"))
                    .addProperty("side", sideParameter())
                    .addProperty("steps", intParameter(
                        "maximum rule applications for the auto strategy; default 2000"))
                    .addProperty("timeout", intParameter("solver-style timeout in seconds"))
                    .addProperty("goal", goalParameter())
                    .addProperty("proof", stringParameter(PROOF_DES))
                    .withRequired(List.of("find", "replace"))
                    .build(),
            true,
            args -> runProbe(args, TOOL_PROBE_EDIT_FORMULA, string(args, "find"),
                string(args, "replace")));
    }

    private static AgentTool explorativeAddFormula() {
        return AgentTool.tool(TOOL_EXPLORATIVE_ADD_FORMULA, ToolCategory.PROOF,
            "explorative: add the formula to the antecedent or succedent of the targeted goal IN"
                + " THE MAIN PROOF via a cut and disable the cut branch representing the case"
                + " without the formula; the theorem is reframed around the added formula (the"
                + " disabled branch should be pruned before the proof can close).",
            Tool.ApprovalRequirement.ASK,
            JsonSchema.builder().withType("object")
                    .addProperty("formula", stringParameter(
                        "the formula to add to the goal's sequent, in KeY syntax"))
                    .addProperty("side", sideParameter())
                    .addProperty("goal", goalParameter())
                    .addProperty("proof", stringParameter(PROOF_DES))
                    .addRequired("formula")
                    .build(),
            false,
            args -> runExplorative(args, TOOL_EXPLORATIVE_ADD_FORMULA, null, null));
    }

    private static AgentTool explorativeEditFormula() {
        return AgentTool.tool(TOOL_EXPLORATIVE_EDIT_FORMULA, ToolCategory.PROOF,
            "explorative: replace the first occurrence of 'find' on the chosen sequent side of"
                + " the targeted goal IN THE MAIN PROOF by 'replace' via a cut, hiding the old"
                + " occurrence on the kept branch and disabling the other cut branch; the theorem"
                + " is reframed around the replaced formula (the disabled branch should be pruned"
                + " before the proof can close).",
            Tool.ApprovalRequirement.ASK,
            JsonSchema.builder().withType("object")
                    .addProperty("find", stringParameter(
                        "the formula to replace, in KeY syntax (must occur on the given side)"))
                    .addProperty("replace", stringParameter(
                        "the formula that replaces it, in KeY syntax"))
                    .addProperty("side", sideParameter())
                    .addProperty("goal", goalParameter())
                    .addProperty("proof", stringParameter(PROOF_DES))
                    .withRequired(List.of("find", "replace"))
                    .build(),
            false,
            args -> runExplorative(args, TOOL_EXPLORATIVE_EDIT_FORMULA, string(args, "find"),
                string(args, "replace")));
    }

    // ------------------------------------------------------------------ probe tools (side proofs)

    /**
     * Runs a probe: resolves the targeted goal, builds the modified root sequent of an isolated
     * side proof (add or edit depending on the arguments), runs the auto strategy under the
     * step/timeout budget and reports whether the goal then closes. The side proof is discarded,
     * so the main proof is unchanged.
     */
    private static String runProbe(Map<String, Object> args, String tool, @Nullable String find,
            @Nullable String replace) {
        boolean edit = find != null;
        var target = ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal"));
        if (target instanceof ProofScriptRunner.All) {
            return singleGoalError(tool);
        }
        Boolean inAntec = side(args, tool);
        if (inAntec == null) {
            return sideError(tool);
        }
        var ref = ProofSelector.proofRef(args);
        if (ref.error() != null) {
            return ref.error();
        }
        Proof proof = ref.proof();
        if (proof == null) {
            return "Error: no proof selected"; // defensive; ProofSelector.proofRef covers this
        }
        Goal goal = ProofScriptRunner.resolveGoal(proof, target);
        if (goal == null) {
            return "Error: " + tool + ": no open goal matches the target";
        }
        var io = new KeyIO(proof.getServices(), goal.getLocalNamespaces());
        var first = parse(io, edit ? find : AgentTool.stringArg(args, "formula"), tool,
            edit ? "find" : "formula");
        if (first.error() != null) {
            return first.error();
        }
        JTerm second = null;
        Sequent sideProofSequent;
        if (edit) {
            var secondResult = parse(io, replace, tool, "replace");
            if (secondResult.error() != null) {
                return secondResult.error();
            }
            second = secondResult.term();
            String err = replaceInSequent(goal, first.term(), second, inAntec, tool);
            if (err != null) {
                return err;
            }
            sideProofSequent = buildEditSequent(goal, first.term(), second, inAntec);
        } else {
            sideProofSequent = buildAddSequent(goal, first.term(), inAntec);
        }
        return runSideProof(tool, args, proof, sideProofSequent, inAntec,
            edit ? "after replacing \"" + find + "\" by \"" + replace + "\" on the "
                    : "with \"" + first.term() + "\" added to the ");
    }

    static String runSideProof(String tool, Map<String, Object> args, Proof proof,
            Sequent sideSequent, boolean inAntec, String situation) {
        var steps = AgentTool.intArg(args, "steps");
        var timeout = AgentTool.intArg(args, "timeout");
        try {
            var env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(proof);
            var starter = SideProofUtil.createSideProof(env, sideSequent, tool + " side proof");
            if (steps != null) {
                starter.setMaxRuleApplications(steps);
            }
            if (timeout != null) {
                starter.setTimeout(timeout * 1000L);
            }
            var result = starter.start();
            int budget = steps != null ? steps : DEFAULT_STEPS;
            if (result.getProof().closed()) {
                return tool + ": " + situation + (inAntec ? "antecedent" : "succedent")
                    + " the goal closes within " + budget + " steps \u2014 TRUE ("
                    + result.getNumberOfAppliedRuleApps() + " rule apps, "
                    + result.getNumberOfClosedGoals() + " goal(s) closed, " + result.reason()
                    + "); the main proof is unchanged (side proof discarded).";
            }
            return tool + ": " + situation + (inAntec ? "antecedent" : "succedent")
                + " the goal does NOT close (" + result.reason() + ", "
                + result.getProof().openGoals().size() + " goal(s) remain open); the main proof is"
                + " unchanged (side proof discarded).";
        } catch (Exception e) {
            return "Error: " + tool + " failed: " + e.getMessage();
        }
    }

    // ------------------------------------------------------------------ explorative tools (main
    // proof)

    /**
     * Runs an explorative edit on the MAIN proof: cut with the new formula, hide the old
     * occurrence on the kept branch (edit case), disable the other cut branch.
     * {@code find} is {@code null} for the plain formula addition.
     */
    private static String runExplorative(Map<String, Object> args, String tool,
            @Nullable String find, @Nullable String replace) {
        boolean edit = find != null;
        var target = ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal"));
        if (target instanceof ProofScriptRunner.All) {
            return singleGoalError(tool);
        }
        Boolean inAntec = side(args, tool);
        if (inAntec == null) {
            return sideError(tool);
        }
        var ref = ProofSelector.proofRef(args);
        if (ref.error() != null) {
            return ref.error();
        }
        Proof proof = ref.proof();
        if (proof == null) {
            return "Error: no proof selected"; // defensive; ProofSelector.proofRef covers this
        }
        Goal goal = ProofScriptRunner.resolveGoal(proof, target);
        if (goal == null) {
            return "Error: " + tool + ": no open goal matches the target";
        }
        var io = new KeyIO(proof.getServices(), goal.getLocalNamespaces());
        var first = parse(io, edit ? find : AgentTool.stringArg(args, "formula"), tool,
            edit ? "find" : "formula");
        if (first.error() != null) {
            return first.error();
        }
        if (edit) {
            var replaced = parse(io, replace, tool, "replace");
            if (replaced.error() != null) {
                return replaced.error();
            }
            JTerm second = replaced.term();
            if (indexOf(sideOf(goal, inAntec), first.term()) < 0) {
                return "Error: " + tool + ": '" + find + "' does not occur on the "
                    + (inAntec ? "antecedent" : "succedent") + " of the targeted goal";
            }
            var services = proof.getServices();
            try {
                return applyCutEdit(tool, goal, proof, services, first.term(), second, inAntec,
                    "replaced \"" + find + "\" by \"" + replace + "\"");
            } catch (Exception e) {
                return "Error: " + tool + " failed: " + e.getMessage();
            }
        }
        var services = proof.getServices();
        try {
            return applyCutEdit(tool, goal, proof, services, null, first.term(), inAntec,
                "added \"" + first.term() + "\"");
        } catch (Exception e) {
            return "Error: " + tool + " failed: " + e.getMessage();
        }
    }

    /**
     * Applies the exploration-style cut edit to the main proof: cut with {@code newFormula},
     * keep the branch carrying it on the target side, hide the {@code find} occurrence on that
     * branch (edits only), disable every other cut branch, and report. {@code find} is
     * {@code null} for the plain formula addition.
     */
    static String applyCutEdit(String tool, Goal goal, Proof proof, Services services,
            @Nullable JTerm find, JTerm newFormula, boolean inAntec, String what)
            throws Exception {
        var initConfig = proof.getEnv().getInitConfigForEnvironment();
        Taclet cut = initConfig.lookupActiveTaclet(new Name("cut"));
        if (cut == null) {
            return "Error: " + tool + ": the 'cut' rule is not active in this proof";
        }
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable cutVar = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(cutVar, newFormula, services, true);
        ImmutableList<Goal> after = goal.apply(app);
        if (after.isEmpty()) {
            return "Error: " + tool + ": the cut produced no goal";
        }
        Goal kept = null;
        for (Goal g : after) {
            if (contains(sideOf(g, inAntec), newFormula)) {
                kept = g;
            }
        }
        if (kept == null) {
            return "Error: " + tool + ": no cut branch carries the new formula on the "
                + (inAntec ? "antecedent" : "succedent");
        }
        for (Goal g : after) {
            if (g != kept) {
                g.setEnabled(false);
            }
        }
        if (find != null) {
            String err = hideOnKeptBranch(tool, kept, proof, services, find, inAntec);
            if (err != null) {
                return err;
            }
        }
        int open = proof.openGoals().size();
        var interactive = proof.openGoals().stream().filter(g -> !g.isAutomatic()).count();
        return tool + ": " + what + " on the " + (inAntec ? "antecedent" : "succedent")
            + " of the targeted goal via cut, and disabled the other cut branch (the case without"
            + " the new formula); " + open + " open goal(s) total, " + interactive
            + " of them interactive/disabled. The theorem is reframed - run auto on the kept"
            + " branch or prune the disabled branch before closing.";
    }

    /**
     * Applies the {@code hide_left}/{@code hide_right} weakening that removes the old formula from
     * the kept cut branch, mirroring the exploration module's edit flow. Returns an error string
     * or {@code null} on success.
     */
    private static @Nullable String hideOnKeptBranch(String tool, Goal goal, Proof proof,
            Services services, JTerm find, boolean inAntec) {
        var side = sideOf(goal, inAntec);
        int idx = indexOf(side, find);
        if (idx < 0) {
            return "Error: " + tool + ": '" + find + "' is no longer on the goal after the cut;"
                + " cannot hide the old occurrence";
        }
        SequentFormula sf = side.asList().skip(idx).head();
        var pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), inAntec);
        String hideRule = inAntec ? "hide_left" : "hide_right";
        Taclet t = proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(
            new Name(hideRule));
        if (!(t instanceof FindTaclet hide)) {
            return "Error: " + tool + ": the '" + hideRule + "' rule is not active in this proof";
        }
        var mc = hide.getMatcher().matchFind(sf.formula(), MatchConditions.EMPTY_MATCHCONDITIONS,
            services);
        if (mc == null) {
            return "Error: " + tool + ": cannot match the '" + hideRule + "' rule at the"
                + " occurrence";
        }
        PosTacletApp hideApp = PosTacletApp.createPosTacletApp(hide, mc, pio, services);
        if (hideApp == null) {
            return "Error: " + tool + ": cannot apply the '" + hideRule + "' rule at the"
                + " occurrence";
        }
        goal.apply(hideApp);
        return null;
    }

    // ------------------------------------------------------------------ sequent construction

    /** The formula list of one sequent side of a goal. */
    private static Semisequent sideOf(Goal goal, boolean inAntec) {
        return inAntec ? goal.sequent().antecedent() : goal.sequent().succedent();
    }

    /** True if the side contains the given term as a formula. */
    private static boolean contains(Semisequent side, JTerm term) {
        for (SequentFormula sf : side) {
            if (sf.formula().equals(term)) {
                return true;
            }
        }
        return false;
    }

    /** The index of the first formula equal to {@code term} on the side, or {@code -1}. */
    private static int indexOf(Semisequent side, JTerm term) {
        var list = side.asList();
        for (int i = 0; i < list.size(); i++) {
            if (list.get(i).formula().equals(term)) {
                return i;
            }
        }
        return -1;
    }

    /** The sequent of an add-probe: the goal's sequent plus the formula on the given side. */
    static Sequent buildAddSequent(Goal goal, JTerm term, boolean inAntec) {
        if (inAntec) {
            var change = goal.sequent().antecedent().insertFirst(new SequentFormula(term));
            return JavaDLSequentKit.createSequent(change.getFormulaList(),
                goal.sequent().succedent().asList());
        }
        var change = goal.sequent().succedent().insertFirst(new SequentFormula(term));
        return JavaDLSequentKit.createSequent(goal.sequent().antecedent().asList(),
            change.getFormulaList());
    }

    /** The sequent of an edit-probe: first occurrence of {@code find} on the side replaced. */
    static Sequent buildEditSequent(Goal goal, JTerm find, JTerm replace, boolean inAntec) {
        Semisequent side = sideOf(goal, inAntec);
        var list = side.asList();
        int idx = indexOf(side, find);
        var changed = list.take(idx).append(new SequentFormula(replace)).append(list.skip(idx + 1));
        if (inAntec) {
            return JavaDLSequentKit.createSequent(changed, goal.sequent().succedent().asList());
        }
        return JavaDLSequentKit.createSequent(goal.sequent().antecedent().asList(), changed);
    }

    // ------------------------------------------------------------------ shared validation

    /** Validates that {@code find} occurs on the given side; error string or {@code null}. */
    private static @Nullable String replaceInSequent(Goal goal, JTerm find, JTerm replace,
            boolean inAntec, String tool) {
        if (indexOf(sideOf(goal, inAntec), find) < 0) {
            return "Error: " + tool + ": '" + find + "' does not occur on the "
                + (inAntec ? "antecedent" : "succedent") + " of the targeted goal";
        }
        return null;
    }

    /**
     * Parses a formula with the goal's namespaces. A blank input yields the "must not be empty"
     * error; a failing parse yields the "cannot parse formula" error; otherwise the term.
     */
    private static ParseResult parse(KeyIO io, @Nullable String text, String tool, String what) {
        if (text == null || text.isBlank()) {
            return new ParseResult(null,
                "Error: " + tool + ": the '" + what + "' parameter must not be empty");
        }
        try {
            return new ParseResult(io.parseExpression(text), null);
        } catch (Exception e) {
            return new ParseResult(null,
                "Error: cannot parse formula '" + text + "': " + e.getMessage());
        }
    }

    /** The outcome of parsing a formula: the term, or a non-{@code null} error message. */
    private record ParseResult(@Nullable JTerm term, @Nullable String error) {
    }

    /** The {@code side} argument as {@code inAntec}, or {@code null} when invalid. */
    private static @Nullable Boolean side(Map<String, Object> args, String tool) {
        String side = AgentTool.stringArg(args, "side");
        if (side == null || side.isBlank()) {
            side = "antecedent";
        }
        if ("antecedent".equals(side)) {
            return Boolean.TRUE;
        }
        if ("succedent".equals(side)) {
            return Boolean.FALSE;
        }
        return null;
    }

    /** The standard single-goal rejection for the {@code "all"} target. */
    private static String singleGoalError(String tool) {
        return "Error: " + tool + " acts on a single goal: use \"branch\" or an index, not"
            + " \"all\".";
    }

    private static String sideError(String tool) {
        return "Error: " + tool + ": 'side' must be \"antecedent\" or \"succedent\"";
    }

    // ------------------------------------------------------------------ schema helpers

    private static JsonSchema stringParameter(String description) {
        return JsonSchema.builder().withType("string").withDescription(description).build();
    }

    private static JsonSchema intParameter(String description) {
        return JsonSchema.builder().withType("integer").withDescription(description).build();
    }

    private static JsonSchema sideParameter() {
        return JsonSchema.builder().withType("string").withDescription(SIDE_DESCRIPTION)
                .withEnum(SIDES).build();
    }

    private static JsonSchema goalParameter() {
        return stringParameter(ProofScriptTools.GOAL_DESCRIPTION);
    }

    private static @Nullable String string(Map<String, Object> args, String key) {
        return AgentTool.stringArg(args, key);
    }
}
