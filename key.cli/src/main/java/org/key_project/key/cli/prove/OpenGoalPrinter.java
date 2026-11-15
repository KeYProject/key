/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.logic.Term;

/**
 * Prints the open goals of a proof in the §6 open-goal layout of the headless interface spec:
 *
 * <pre>
 * CONTRACT &lt;NAME&gt;
 * OPEN-GOAL-COUNT &lt;N&gt;
 * GOAL &lt;id&gt; &lt;position-path&gt;
 *   &lt;antecedent-term&gt;
 *   ==&gt; &lt;succedent-term&gt;
 *
 * </pre>
 *
 * The {@code CONTRACT} label line names the contract the proof was created for; a run over
 * several contracts prints one such section per contract, in selection order. The
 * {@code OPEN-GOAL-COUNT} line always carries the true total number of open goals; {@code MAX}
 * only bounds the number of printed {@code GOAL} blocks ({@code 0} = no bound). Each formula is
 * printed on its own line (embedded line breaks are escaped as literal {@code \n}); by default a
 * formula longer than {@link #DEFAULT_MAX_TERM_LENGTH} characters is truncated with a {@code ...}
 * marker, which {@code --no-truncate-formulas} disables. Goals are printed in the deterministic
 * iteration order of {@link Proof#openGoals()}.
 */
public final class OpenGoalPrinter {

    /** The default bound of {@code --print-open-goals} when the option is given without a value. */
    public static final int DEFAULT_MAX_GOALS = 10;

    /** The default maximum length (in characters) of one printed formula before truncation. */
    public static final int DEFAULT_MAX_TERM_LENGTH = 200;

    /**
     * The position path of the proof root, which is also the §7.1 {@code at} anchor of the root
     * goal: the root can only be an open goal in the trivial proof state where it has no children,
     * so {@code 1} can never denote a child node at the same time.
     */
    public static final String ROOT_POSITION = "1";

    private final PrintWriter out;

    private final int maxGoals;

    private final boolean truncateFormulas;

    /**
     * Creates a printer with the default bound of {@value #DEFAULT_MAX_GOALS} blocks and
     * formula truncation enabled.
     *
     * @param out the writer the open-goal output is printed to (stdout of the command)
     */
    public OpenGoalPrinter(PrintWriter out) {
        this(out, DEFAULT_MAX_GOALS, true);
    }

    /**
     * Creates an open-goal printer.
     *
     * @param out the writer the open-goal output is printed to (stdout of the command)
     * @param maxGoals the maximum number of {@code GOAL} blocks to print, or {@code 0} for no
     *        bound
     * @param truncateFormulas whether formulas longer than {@link #DEFAULT_MAX_TERM_LENGTH}
     *        characters are truncated with a {@code ...} marker
     */
    public OpenGoalPrinter(PrintWriter out, int maxGoals, boolean truncateFormulas) {
        this.out = out;
        this.maxGoals = Math.max(0, maxGoals);
        this.truncateFormulas = truncateFormulas;
    }

    /**
     * Prints the open goals of the proof: a {@code CONTRACT <name>} label line, an
     * {@code OPEN-GOAL-COUNT} line with the true total, followed by at most {@code maxGoals}
     * {@code GOAL} blocks ({@code 0} = no bound), each terminated by a blank line.
     *
     * @param contract the contract the proof was created for (its canonical name is printed as
     *        the section label)
     * @param proof the proof whose open goals are printed
     */
    public void print(Contract contract, Proof proof) {
        out.println("CONTRACT " + contract.getName());
        List<Goal> goals = new ArrayList<>();
        for (Goal goal : proof.openGoals()) {
            goals.add(goal);
        }
        out.println("OPEN-GOAL-COUNT " + goals.size());
        int limit = maxGoals == 0 ? goals.size() : Math.min(maxGoals, goals.size());
        for (int i = 0; i < limit; i++) {
            printGoal(goals.get(i), i, proof);
        }
    }

    private void printGoal(Goal goal, int id, Proof proof) {
        String path = positionPath(goal.node(), proof.root());
        out.println("GOAL " + id + " " + path);
        for (var sf : goal.sequent().antecedent()) {
            out.println("  " + renderTerm(sf.formula(), proof));
        }
        List<String> succedent = new ArrayList<>();
        for (var sf : goal.sequent().succedent()) {
            succedent.add(renderTerm(sf.formula(), proof));
        }
        if (succedent.isEmpty()) {
            out.println("  ==>");
        } else {
            out.println("  ==> " + succedent.get(0));
            for (int i = 1; i < succedent.size(); i++) {
                out.println("  " + succedent.get(i));
            }
        }
        out.println();
    }

    /**
     * Computes the position path of a goal node: the 1-based child indices from the proof root
     * to the node, dot-separated (for example {@code 1.2.1}). The path of the root itself is
     * {@code 1}, matching the {@code ROOT_POSITION} anchor of the §7.1 {@code at <position-path>}
     * command: a node with children can never be an open goal, so {@code 1} is unambiguous.
     * <p>
     * Every returned path therefore matches {@code ^[1-9][0-9.]*$} (acceptance F2).
     *
     * @param node the goal node
     * @param root the root node of the goal's proof
     * @return the dot-separated position path ({@code 1} for the root)
     * @throws IllegalArgumentException if {@code node} is not a descendant of {@code root}
     */
    public static String positionPath(Node node, Node root) {
        if (node == root) {
            return ROOT_POSITION;
        }
        StringBuilder sb = new StringBuilder();
        Node cur = node;
        while (cur != root) {
            Node parent = cur.parent();
            if (parent == null) {
                throw new IllegalArgumentException(
                    "node is not part of the proof of the given root");
            }
            sb.insert(0, (parent.getChildNr(cur) + 1) + (sb.isEmpty() ? "" : "."));
            cur = parent;
        }
        return sb.toString();
    }

    private String renderTerm(Term term, Proof proof) {
        String printed = LogicPrinter.quickPrintTerm((JTerm) term, proof.getServices());
        String flat = printed.replace("\r\n", "\n").replace('\r', '\n').replace("\n", "\\n");
        if (truncateFormulas && flat.length() > DEFAULT_MAX_TERM_LENGTH) {
            flat = flat.substring(0, DEFAULT_MAX_TERM_LENGTH - 3) + "...";
        }
        return flat;
    }
}
