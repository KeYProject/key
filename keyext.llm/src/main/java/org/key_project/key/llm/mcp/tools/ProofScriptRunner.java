/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptBlock;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.scripts.ScriptException;

import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * Shared machinery for the proof-manipulation tools: a uniform proof-script runner with a
 * consistent result report ("N goal(s) closed, M open goal(s) remain"), and goal targeting that
 * all proof tools speak ({@code "branch"} - the first open goal of the current branch,
 * {@code "all"} - every open goal, or a 0-based index, negative = from the end).
 * <p>
 * Goal targeting is delegated to the {@code select} proof-script command (for indices) and the
 * {@code onAll} wrapper (for {@code "all"}): {@code select number:<n>} makes the engine run the
 * following command on the selected goal, {@code onAll { ... }} runs a single command on every
 * open goal. The proof lives on the GUI thread's selected proof unless the tool passes a
 * {@code proof} identifier resolved via {@link ProofSelector #proofRef(Map)}.
 *
 * @author Alexander Weigl
 */
public final class ProofScriptRunner {

    private ProofScriptRunner() {
    }

    // ------------------------------------------------------------------ goal targeting

    /** How a tool call selects the goal(s) its command applies to. */
    public sealed interface GoalTarget permits Branch, All, Index {
    }

    /** The first open goal of the current branch (the default). */
    public record Branch() implements GoalTarget {
    }

    /** Every open goal (wrapped in an {@code onAll} block). */
    public record All() implements GoalTarget {
    }

    /** A single open goal, selected by its 0-based index (negative = from the end). */
    public record Index(int number) implements GoalTarget {
    }

    /**
     * Parses the common {@code goal} tool parameter: {@code null}/{@code blank}/{@code "branch"}
     * selects the current branch, {@code "all"} every open goal, an integer the goal with that
     * index.
     *
     * @throws IllegalArgumentException on anything else
     */
    public static GoalTarget parseGoal(@Nullable String goal) {
        if (goal == null || goal.isBlank() || "branch".equals(goal)) {
            return new Branch();
        }
        if ("all".equals(goal)) {
            return new All();
        }
        try {
            return new Index(Integer.parseInt(goal.trim()));
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException("'goal' must be \"branch\" (default), \"all\" or"
                + " an open-goal index, got: " + goal);
        }
    }

    /** A {@code select number:<n>} command prefix; the next command runs on that goal. */
    public static ScriptCommandAst selectGoal(int number) {
        return new ScriptCommandAst("select", Map.of("number", number), List.of());
    }

    /** Wraps a command in {@code onAll { ... }} so it runs on every open goal. */
    public static ScriptCommandAst onAll(ScriptCommandAst command) {
        return new ScriptCommandAst("onAll", Map.of(),
            List.of(new ScriptBlock(List.of(command), null)));
    }

    /**
     * Prepares the command list for a goal target: the command itself, optionally prefixed with a
     * {@code select} (index) or wrapped into {@code onAll} (all goals).
     */
    public static List<ScriptCommandAst> target(GoalTarget target, ScriptCommandAst command) {
        if (target instanceof Branch) {
            return List.of(command);
        }
        if (target instanceof Index index) {
            return List.of(selectGoal(index.number()), command);
        }
        return List.of(onAll(command));
    }

    // ------------------------------------------------------------------ goal resolution

    /**
     * The open goals of a proof in the order the {@code select number:<n>} script command numbers
     * them: a depth-first walk from the root that counts only the open, automatic goals.
     * <p>
     * This is the ordering behind the {@code goal} parameter of every proof tool: a {@code goal}
     * index selects the goal at this position, {@code "branch"} the first one.
     */
    public static List<Goal> goalsInSelectOrder(Proof proof) {
        List<Goal> ordered = new ArrayList<>();
        ImmutableList<Goal> openGoals = proof.openGoals();
        Deque<Node> choices = new LinkedList<>();
        Node node = proof.root();
        while (node != null) {
            if (node.isClosed()) {
                return ordered;
            }
            int childCount = node.childrenCount();
            switch (childCount) {
                case 0 -> {
                    Goal goal = openGoalAt(openGoals, node);
                    if (goal != null && goal.isAutomatic()) {
                        ordered.add(goal);
                    }
                    node = choices.pollLast();
                }
                case 1 -> node = node.child(0);
                default -> {
                    Node next = null;
                    for (int i = 0; i < childCount; i++) {
                        Node child = node.child(i);
                        if (!child.isClosed()) {
                            if (next == null) {
                                next = child;
                            } else {
                                choices.add(child);
                            }
                        }
                    }
                    if (next == null) {
                        return ordered;
                    }
                    node = next;
                }
            }
        }
        return ordered;
    }

    private static @Nullable Goal openGoalAt(ImmutableList<Goal> openGoals, Node node) {
        for (Goal goal : openGoals) {
            if (goal.node() == node) {
                return goal;
            }
        }
        return null;
    }

    /**
     * Resolves a parsed {@link GoalTarget} to an actual goal of a proof, using the same numbering
     * as {@code select}: {@code branch} = the first open automatic goal, an index selects by
     * 0-based position (negative = from the end). Returns {@code null} when the target does not
     * name an open automatic goal.
     */
    public static @Nullable Goal resolveGoal(Proof proof, GoalTarget target) {
        List<Goal> ordered = goalsInSelectOrder(proof);
        if (target instanceof Branch) {
            return ordered.isEmpty() ? null : ordered.getFirst();
        }
        if (target instanceof Index index) {
            int i = index.number() < 0 ? ordered.size() + index.number() : index.number();
            return i >= 0 && i < ordered.size() ? ordered.get(i) : null;
        }
        return null; // "all" is never a single goal
    }

    // ------------------------------------------------------------------ execution + reporting

    /**
     * Runs the commands on the proof addressed by the tool arguments (the {@code proof} parameter
     * or the selected proof) and reports the outcome uniformly.
     */
    public static String run(Map<String, Object> args, String summaryName,
            List<ScriptCommandAst> commands) {
        var ref = ProofSelector.proofRef(args);
        if (ref.error() != null) {
            return ref.error();
        }
        return run(ref.proof(), summaryName, commands);
    }

    /**
     * Executes the commands via the {@link ProofScriptEngine} (the same machinery as the "Apply
     * Script" action) and reports how many open goals were closed.
     */
    public static String run(@Nullable Proof proof, String summaryName,
            List<ScriptCommandAst> commands) {
        if (proof == null) {
            return "Error: no proof selected"; // defensive; ProofSelector.proofRef covers this
        }
        int before = proof.openGoals().size();
        var mainWindow = MainWindow.getInstance();
        if (mainWindow == null || mainWindow.getMediator() == null) {
            return "Error: no main window available to run proof scripts";
        }
        var ui = mainWindow.getMediator().getUI();
        try {
            new ProofScriptEngine(proof).execute(ui, commands);
        } catch (ScriptException e) {
            return "Error: " + e.getMessage();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return "Error: proof search interrupted";
        }
        int after = proof.openGoals().size();
        int closed = before - after;
        return summaryName + ": " + closed + " goal(s) closed, " + after + " open goal(s) remain"
            + (after == 0 ? " - the proof is closed" : "") + ".";
    }
}
