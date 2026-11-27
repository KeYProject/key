/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.SideProofUtil;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * The proof forking tool {@code fork_proof}: it creates an independent copy ("fork") of a proof at
 * the sequent of a chosen goal via the side-proof machinery ({@link SideProofUtil},
 * {@link de.uka.ilkd.key.util.ProofStarter}) and registers it so it can be addressed by index or
 * name like any other open proof. The fork is a brand-new proof whose root sequent is the sequent
 * of the targeted goal; it appears in {@code list_proofs} and can be worked on freely (via the
 * {@code proof} parameter of every other proof tool) without touching the original proof - the
 * canonical side proof for experimentation. Registration happens through the mediator's
 * currently-opened-proofs list, the same list {@link ProofSelector} resolves {@code proof}
 * identifiers against.
 *
 * @author Alexander Weigl
 */
public final class ProofForkTools implements AgentToolProvider {
    /** The {@code fork_proof} tool. */
    public static final String TOOL_FORK_PROOF = "fork_proof";

    /** Counter that keeps the auto-generated fork names unique across the whole session. */
    private static final AtomicInteger FORK_COUNTER = new AtomicInteger();

    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(TOOL_FORK_PROOF, ToolCategory.PROOF,
                "create an independent copy of the proof at the sequent of the targeted goal,"
                    + " register it (it appears in `list_proofs`), and leave it untouched for side"
                    + " experiments; the original proof is not modified",
                Tool.ApprovalRequirement.ASK,
                AgentTool.schema(
                    "goal",
                    JsonSchema.builder().withType("string")
                            .withDescription(ProofScriptTools.GOAL_DESCRIPTION).build(),
                    "name",
                    JsonSchema.builder().withType("string")
                            .withDescription("a name for the forked proof; defaults to"
                                + " \"<original>-fork-<n>\"")
                            .build(),
                    "proof",
                    JsonSchema.builder().withType("string")
                            .withDescription("proof identifier from list_proofs; defaults to the"
                                + " selected proof")
                            .build()),
                false,
                args -> {
                    var target = ProofScriptRunner.parseGoal(AgentTool.stringArg(args, "goal"));
                    if (target instanceof ProofScriptRunner.All) {
                        return "Error: fork_proof acts on a single goal: use \"branch\" or an"
                            + " index, not \"all\".";
                    }
                    var ref = ProofSelector.proofRef(args);
                    if (ref.error() != null) {
                        return ref.error();
                    }
                    var proof = ref.proof();
                    if (proof == null) {
                        return "Error: no proof selected";
                    }
                    Goal goal = ProofScriptRunner.resolveGoal(proof, target);
                    if (goal == null) {
                        return "Error: fork_proof: no open goal matches the target";
                    }
                    var name = AgentTool.stringArg(args, "name");
                    if (name == null || name.isBlank()) {
                        name = proof.name().toString() + "-fork-" + FORK_COUNTER.incrementAndGet();
                    }
                    try {
                        var env =
                            SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(proof);
                        var starter = SideProofUtil.createSideProof(env, goal.sequent(), name);
                        Proof fork = starter.getProof(); // @Nullable - guard null
                        if (fork == null) {
                            return "Error: fork_proof: no fork proof was created";
                        }
                        var mainWindow = MainWindow.getInstance();
                        if (mainWindow == null) {
                            return "Error: no main window available to fork a proof";
                        }
                        var opened = mainWindow.getMediator().getCurrentlyOpenedProofs();
                        opened.add(fork);
                        int index = opened.indexOf(fork);
                        int openGoals = fork.openGoals().size();
                        String targetText = switch (target) {
                            case ProofScriptRunner.Index idx -> "index " + idx.number();
                            default -> "branch";
                        };
                        return "fork_proof: created proof \"" + name + "\" (index " + index
                            + " in list_proofs) from goal " + targetText + "; it has " + openGoals
                            + " open goal(s) and the original proof is unchanged. Pass the index"
                            + " as the 'proof' parameter to work on the fork.";
                    } catch (Exception e) {
                        return "Error: fork_proof failed: " + e.getMessage();
                    }
                }));
    }
}
