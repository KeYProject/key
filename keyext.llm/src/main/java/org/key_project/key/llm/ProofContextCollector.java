/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.util.ArrayList;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.Nullable;

/**
 * Collects the current proof state as compact text blocks that can be attached to a prompt or
 * returned by the {@code get_proof_context} tool.
 * <p>
 * All outputs are capped by the context-budget settings in {@link LlmSettings}.
 *
 * @author Alexander Weigl
 */
public final class ProofContextCollector {
    private ProofContextCollector() {
    }

    public static String proofName(Proof proof) {
        return proof.name() != null ? proof.name().toString() : "<unnamed proof>";
    }

    /**
     * Short status line: number of open/closed goals and proof steps.
     */
    public static String proofStatus(Proof proof) {
        int open = proof.openGoals().size();
        int closed = proof.closedGoals().size();
        int steps = proof.countNodes();
        return "Proof \"" + proofName(proof) + "\": " + open + " open goal(s), " + closed
            + " closed, " + steps + " nodes.";
    }

    /** The sequent of a node or of the first open goal, formatted, capped in length. */
    public static String sequentText(@Nullable Node node, @Nullable Proof proof) {
        var seq = node != null && node.sequent() != null ? node.sequent()
                : firstOpenGoalSequent(proof);
        if (seq == null) {
            return "(no sequent available)";
        }
        return cap(seq.toString());
    }

    private static @Nullable Sequent firstOpenGoalSequent(@Nullable Proof proof) {
        if (proof == null) {
            return null;
        }
        for (Goal g : proof.openGoals()) {
            return g.node().sequent();
        }
        return null;
    }

    /** Up to {@code max} open-goal sequents, each capped. */
    public static String openGoalsSummary(Proof proof, int max) {
        var sb = new StringBuilder();
        int i = 0;
        for (Goal g : proof.openGoals()) {
            if (sb.length() > 0) {
                sb.append('\n');
            }
            sb.append("Goal ").append(++i).append(":\n").append(cap(g.node().sequent().toString()));
            if (i >= max) {
                sb.append("\n... more open goals omitted");
                break;
            }
        }
        if (sb.length() == 0) {
            sb.append("(no open goals)");
        }
        return sb.toString();
    }

    /**
     * The computation path (after Harel): the sequence of applied rules on the path from the proof
     * root down to the selected node. Bounded to {@code maxSteps} entries.
     */
    public static String computePath(@Nullable Node node, int maxSteps) {
        if (node == null) {
            return "(no selected node)";
        }
        var names = new ArrayList<String>();
        Node current = node;
        int hops = 0;
        while (current != null && current.parent() != null && hops < maxSteps) {
            var ruleApp = current.getAppliedRuleApp();
            if (ruleApp != null && ruleApp.rule() != null) {
                names.add(ruleApp.rule().name().toString());
            }
            current = current.parent();
            hops++;
        }
        if (names.isEmpty()) {
            return "(computation path not available for this node)";
        }
        var sb = new StringBuilder("Computation path (root to selected node):\n");
        for (int idx = names.size() - 1; idx >= 0; idx--) {
            sb.append("  ").append(names.get(idx)).append('\n');
        }
        if (hops >= maxSteps) {
            sb.append("  ... truncated");
        }
        return sb.toString();
    }

    /** Model directories and class paths, if available. */
    public static String modelInfo(Proof proof) {
        var javaModel = proof.getEnv().getServicesForEnvironment().getJavaModel();
        if (javaModel == null) {
            return "(no Java model)";
        }
        var sb = new StringBuilder("Java model:");
        var dir = javaModel.getModelDir();
        sb.append("\n  model dir: ").append(dir == null ? "(none)" : dir);
        var classPath = javaModel.getClassPath();
        if (classPath != null && !classPath.isEmpty()) {
            sb.append("\n  classpath: ").append(cap(classPath.toString(), 2000));
        }
        var boot = javaModel.getBootClassPath();
        if (boot != null) {
            sb.append("\n  boot classpath: ").append(boot);
        }
        return sb.toString();
    }

    /**
     * One consolidated context block used when "attach proof context" is enabled or requested by
     * the {@code get_proof_context} tool.
     */
    public static String contextBlock(@Nullable Proof proof, @Nullable Node selectedNode) {
        var settings = LlmSettings.INSTANCE;
        var sb = new StringBuilder();
        sb.append("Current proof state:\n");
        if (proof == null) {
            sb.append("(no proof loaded)");
            return sb.toString();
        }
        sb.append(proofStatus(proof)).append('\n');
        sb.append("Current sequent:\n").append(sequentText(selectedNode, proof)).append('\n');
        sb.append("Open goals:\n")
                .append(openGoalsSummary(proof, settings.getProofContextMaxSequents()))
                .append('\n');
        sb.append(modelInfo(proof)).append('\n');
        sb.append(computePath(selectedNode, 100)).append('\n');
        return cap(sb.toString(), settings.getProofContextMaxChars());
    }

    private static String cap(String s) {
        return cap(s, LlmSettings.INSTANCE.getProofContextMaxChars());
    }

    private static String cap(String s, int max) {
        if (s == null) {
            return "";
        }
        if (s.length() > max) {
            return s.substring(0, max) + "\n... [truncated]";
        }
        return s;
    }
}
