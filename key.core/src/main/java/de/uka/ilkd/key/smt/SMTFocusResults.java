/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.Arrays;
import java.util.HashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Compute unsat core from SMT problems and hide all irrelevant formulas from sequent.
 * Temporary hack to evaluate the potential of such a technique
 *
 * @author Mattias Ulbrich
 */
public final class SMTFocusResults {
    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(SMTFocusResults.class);

    private SMTFocusResults() {

    }

    /**
     * Try to focus the sequent using the unsat core provided by one of the SMT solvers run.
     * This will hide all formulas not present in the unsat core using hide_left and hide_right
     * applications.
     *
     * @param smtProblem SMT solver results
     * @param services services
     * @return whether the sequent was 'focused'
     */
    public static boolean focus(SMTProblem smtProblem, Services services) {

        ImmutableList<PosInOccurrence> unsatCore = getUnsatCore(smtProblem);
        if (unsatCore == null) {
            return false;
        }

        Goal goal = smtProblem.getGoal();
        // cache the goal node, because we will apply rules on the goal
        // (changing the result of goal.node())
        Node goalNode = smtProblem.getNode();

        FindTaclet hideLeft = (FindTaclet) goalNode.proof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(new Name("hide_left"));

        FindTaclet hideRight = (FindTaclet) goalNode.proof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(new Name("hide_right"));

        Semisequent antecedent = goalNode.sequent().antecedent();
        Semisequent succedent = goalNode.sequent().succedent();

        int i = 1;
        for (SequentFormula sf : antecedent) {
            PosInOccurrence pio =
                PosInOccurrence.findInSequent(goalNode.sequent(), i, PosInTerm.getTopLevel());
            if (!unsatCore.contains(pio)) {
                // TODO: ugly way of acessing. Can be done better?!
                SchemaVariable schema = hideLeft.collectSchemaVars().iterator().next();
                TacletApp app = PosTacletApp.createPosTacletApp(hideLeft, new MatchConditions(),
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                    services);
                app = app.addCheckedInstantiation(schema, sf.formula(), services, true);
                goal = goal.apply(app).iterator().next();
            }
            i++;
        }

        for (SequentFormula sf : succedent) {
            PosInOccurrence pio =
                PosInOccurrence.findInSequent(goalNode.sequent(), i, PosInTerm.getTopLevel());
            if (!unsatCore.contains(pio)) {
                // TODO: ugly way of acessing. Can be done better?!
                SchemaVariable schema = hideRight.collectSchemaVars().iterator().next();
                TacletApp app =
                    PosTacletApp.createPosTacletApp(hideRight, new MatchConditions(),
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                        services);
                app = app.addCheckedInstantiation(schema, sf.formula(), services, true);
                goal = goal.apply(app).iterator().next();
            }
            i++;
        }

        return true;

    }

    /**
     * Try to get the unsat core provided by one of the SMT solvers run.
     * This will only return formulas from the sequent, not any other input provided to the SMT
     * solver.
     *
     * @param problem SMT solver results
     * @return formula collection or null if the solver did not produce an unsat core
     */
    public static ImmutableList<PosInOccurrence> getUnsatCore(SMTProblem problem) {

        SMTSolver solver = problem.getSuccessfulSolver();

        if (solver.getFinalResult().isValid() != ThreeValuedTruth.VALID) {
            return null;
        }

        String[] lines = solver.getRawSolverOutput().split("\n");
        String lastLine = lines[lines.length - 1];

        LOGGER.info("Analyzing unsat core: {}", lastLine);

        Integer[] numbers;
        if (lastLine.matches("\\(.*\\)")) {
            // Z3 unsat core format: all labels on one line
            numbers = parseZ3Format(lastLine);
        } else if (lastLine.equals(")")) {
            // CVC5 unsat core format: each label on a separate line
            numbers = parseCVC5Format(lines);
        } else {
            // unknown format / no unsat core produced
            return null;
        }

        Node goalNode = problem.getNode();

        HashSet<Integer> unsatCore = new HashSet<>(Arrays.asList(numbers));
        ImmutableList<PosInOccurrence> unsatCoreFormulas = ImmutableSLList.nil();

        Semisequent antecedent = goalNode.sequent().antecedent();
        int i = 1;
        for (SequentFormula sf : antecedent) {
            if (unsatCore.contains(i)) {
                unsatCoreFormulas = unsatCoreFormulas.prepend(PosInOccurrence
                        .findInSequent(goalNode.sequent(), i, PosInTerm.getTopLevel()));
            }
            i++;
        }

        Semisequent succedent = goalNode.sequent().succedent();
        for (SequentFormula sf : succedent) {
            if (unsatCore.contains(i)) {
                unsatCoreFormulas = unsatCoreFormulas.prepend(PosInOccurrence
                        .findInSequent(goalNode.sequent(), i, PosInTerm.getTopLevel()));
            }
            i++;
        }

        return unsatCoreFormulas;
    }

    /**
     * Parse Z3-style unsat core output: (L_1 L_2 L_17)
     *
     * @param lastLine unsat core line
     * @return list of labels referenced in the unsat core
     */
    static Integer[] parseZ3Format(String lastLine) {
        lastLine = lastLine.substring(1, lastLine.length() - 1);

        String[] labels = lastLine.trim().split(" +");
        Integer[] numbers = new Integer[labels.length];
        for (int i = 0; i < numbers.length; i++) {
            numbers[i] = Integer.parseInt(labels[i].substring(2));
        }
        return numbers;
    }

    /**
     * Parse CVC5-style unsat core output:
     *
     * <pre>
     *     (
     *     L_5
     *     L_42
     *     )
     * </pre>
     *
     * @param lines CVC5 output
     * @return list of labels referenced in unsat core
     */
    static Integer[] parseCVC5Format(String[] lines) {
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].equals("(")) {
                Integer[] numbers = new Integer[lines.length - 2 - i];
                for (int j = i + 1; j < lines.length - 1; j++) {
                    numbers[j - i - 1] = Integer.parseInt(lines[j].substring(2));
                }
                return numbers;
            }
        }
        return null;
    }
}
