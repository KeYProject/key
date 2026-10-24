/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.util.SideProofUtil;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.ToolCategory;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

/**
 * The exploration tools {@code explore_assumption} and {@code explore_formula}: they answer "is
 * the targeted goal provable IF a given formula is available?" by running the default auto
 * strategy on an ISOLATED SIDE PROOF, never touching the main proof.
 * <p>
 * The side proof is built with {@link SideProofUtil}: the proof environment is cloned with its
 * own {@code OneStepSimplifier}, and the root sequent of the side proof is the targeted goal's
 * sequent extended by the given formula (added to the antecedent for {@code explore_assumption},
 * to the succedent for {@code explore_formula}). The auto strategy then runs under a step/timeout
 * budget via {@code ProofStarter}; the side proof is never registered anywhere and is discarded
 * (garbage-collected) after the run — by construction the main proof is unchanged.
 *
 * @author Alexander Weigl
 */
public final class ExploreProofTools implements AgentToolProvider {
    /** The {@code explore_assumption} tool. */
    public static final String TOOL_EXPLORE_ASSUMPTION = "explore_assumption";
    /** The {@code explore_formula} tool. */
    public static final String TOOL_EXPLORE_FORMULA = "explore_formula";

    /** The default rule-application budget of the auto strategy on the side proof. */
    private static final int DEFAULT_STEPS = 2000;

    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(TOOL_EXPLORE_ASSUMPTION, ToolCategory.PROOF,
                "run the KeY auto strategy on an isolated side proof (built with SideProofUtil)"
                    + " of the targeted goal with the given formula ADDED AS ASSUMPTION to the"
                    + " antecedent, and report whether the goal then closes under the step/timeout"
                    + " budget; the main proof is never modified.",
                JsonSchema.builder().withType("object")
                    .addProperty("formula",
                        JsonSchema.builder().withType("string")
                                .withDescription("the formula to assume in the antecedent of a"
                                    + " side proof, in KeY syntax")
                                .build())
                    .addProperty("steps",
                        JsonSchema.builder().withType("integer")
                                .withDescription("maximum rule applications for the auto"
                                    + " strategy; default 2000")
                                .build())
                    .addProperty("timeout",
                        JsonSchema.builder().withType("integer")
                                .withDescription("solver-style timeout in seconds").build())
                    .addProperty("goal",
                        JsonSchema.builder().withType("string")
                                .withDescription(ProofScriptTools.GOAL_DESCRIPTION).build())
                    .addProperty("proof",
                        JsonSchema.builder().withType("string")
                                .withDescription("proof identifier from list_proofs; defaults to"
                                    + " the selected proof")
                                .build())
                    .addRequired("formula")
                    .build(),
                true,
                args -> runSideProof(args, TOOL_EXPLORE_ASSUMPTION, true)),
            AgentTool.tool(TOOL_EXPLORE_FORMULA, ToolCategory.PROOF,
                "check whether the targeted goal closes if the given formula were part of the"
                    + " succedent (a weakening): run the KeY auto strategy on an isolated side"
                    + " proof (built with SideProofUtil) whose succedent contains the formula and"
                    + " report whether the formula alone entails the goal under the step/timeout"
                    + " budget; the main proof is never modified.",
                JsonSchema.builder().withType("object")
                    .addProperty("formula",
                        JsonSchema.builder().withType("string")
                                .withDescription("the formula to add to the succedent of a side"
                                    + " proof, in KeY syntax")
                                .build())
                    .addProperty("steps",
                        JsonSchema.builder().withType("integer")
                                .withDescription("maximum rule applications for the auto"
                                    + " strategy; default 2000")
                                .build())
                    .addProperty("timeout",
                        JsonSchema.builder().withType("integer")
                                .withDescription("solver-style timeout in seconds").build())
                    .addProperty("goal",
                        JsonSchema.builder().withType("string")
                                .withDescription(ProofScriptTools.GOAL_DESCRIPTION).build())
                    .addProperty("proof",
                        JsonSchema.builder().withType("string")
                                .withDescription("proof identifier from list_proofs; defaults to"
                                    + " the selected proof")
                                .build())
                    .addRequired("formula")
                    .build(),
                true,
                args -> runSideProof(args, TOOL_EXPLORE_FORMULA, false)));
    }

    /**
     * Runs the exploration: resolves the targeted goal, parses the formula, builds the side proof
     * (formula added to the antecedent when {@code asAssumption}, else to the succedent), runs the
     * auto strategy under the step/timeout budget and reports whether the goal then closes.
     * <p>
     * The side proof is never registered anywhere and discarded after the run, so the main proof
     * is unchanged.
     */
    private static String runSideProof(Map<String, Object> args, String tool, boolean asAssumption) {
        var target = ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal"));
        if (target instanceof ProofScriptRunner.All) {
            return "Error: " + tool
                + " acts on a single goal: use \"branch\" or an index, not \"all\".";
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
        var formulaText = AgentTool.stringArg(args, "formula");
        if (formulaText == null || formulaText.isBlank()) {
            return "Error: " + tool + ": the 'formula' parameter must not be empty";
        }
        JTerm term;
        try {
            var io = new KeyIO(proof.getServices(), goal.getLocalNamespaces());
            term = io.parseExpression(formulaText);
        } catch (Exception e) {
            return "Error: cannot parse formula '" + formulaText + "': " + e.getMessage();
        }
        Sequent side;
        if (asAssumption) {
            var change = goal.sequent().antecedent().insertFirst(new SequentFormula(term));
            side = JavaDLSequentKit.createSequent(change.getFormulaList(),
                goal.sequent().succedent().asList());
        } else {
            var change = goal.sequent().succedent().insertFirst(new SequentFormula(term));
            side = JavaDLSequentKit.createSequent(goal.sequent().antecedent().asList(),
                change.getFormulaList());
        }
        var steps = AgentTool.intArg(args, "steps");
        var timeout = AgentTool.intArg(args, "timeout");
        try {
            var env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(proof);
            var starter = SideProofUtil.createSideProof(env, side, tool + " side proof");
            if (steps != null) {
                starter.setMaxRuleApplications(steps);
            }
            if (timeout != null) {
                starter.setTimeout(timeout * 1000L);
            }
            var result = starter.start();
            boolean closed = result.nonCloseableGoal() == null;
            int budget = steps != null ? steps : DEFAULT_STEPS;
            String placed = asAssumption ? "as hypothesis" : "in the succedent";
            if (closed) {
                return tool + ": with \"" + formulaText + "\" " + placed
                    + " the goal closes within " + budget + " steps \u2014 TRUE ("
                    + result.getNumberOfAppliedRuleApps() + " rule apps, "
                    + result.getNumberOfClosedGoals() + " goal(s) closed, " + result.reason()
                    + "); the main proof is unchanged (side proof discarded).";
            }
            int remaining = result.getProof().openGoals().size();
            return tool + ": with \"" + formulaText + "\" " + placed
                + " the goal does NOT close (" + result.reason() + ", " + remaining
                + " goal(s) remain non-closeable); the main proof is unchanged (side proof"
                + " discarded).";
        } catch (Exception e) {
            return "Error: " + tool + " failed: " + e.getMessage();
        }
    }
}
