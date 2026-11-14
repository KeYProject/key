/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a problem that can be passed to a solver. This class was introduced because the SMT
 * module must handle both goals and terms.<br>
 * Each <code>SMTProblem</code> is related to a set of solvers that are used to solve this problem.
 *
 */
@NullMarked
public class SMTProblem {

    private final JTerm term;
    private final Collection<SMTSolver> solvers = new LinkedList<>();
    private final @Nullable Goal goal;
    private final @Nullable Node node;
    private @Nullable Sequent sequent;
    private final String name;

    /* ############# public interface ############# */
    /**
     * Creates out of a proof object several SMT problems. For each open goal a new SMT problem is
     * created.
     */
    public static Collection<SMTProblem> createSMTProblems(Proof proof) {
        LinkedList<SMTProblem> problems = new LinkedList<>();
        for (Goal goal : proof.openGoals()) {
            problems.add(new SMTProblem(goal));
        }
        return problems;
    }

    /**
     * Returns the term that is related to this problem. If the problem was initialized with a goal,
     * the goal is transformed to the term that can be accessed by this method.
     */
    public JTerm getTerm() {
        return term;
    }

    /** Returns the solvers that are related to the problem */
    public Collection<SMTSolver> getSolvers() {
        return solvers;
    }

    /**
     * The term conversion operates on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here because it only reads the
     * {@link #goal} assigned just above, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public SMTProblem(Goal goal) {
        this.goal = goal;
        this.node = goal.node();
        name = "Goal " + goal.node().serialNr();
        term = goalToTerm(goal);
    }

    public SMTProblem(Sequent s, Services services) {
        this.goal = null;
        this.node = null;
        this.sequent = s;
        name = "Sequent " + s.toString();
        this.term = sequentToTerm(s, services);
    }

    public SMTProblem(JTerm t) {
        this.goal = null;
        this.node = null;
        name = "Term " + t.toString();
        this.term = t;
    }

    public @Nullable Goal getGoal() {
        return goal;
    }

    public @Nullable Node getNode() {
        return node;
    }

    public @Nullable Sequent getSequent() {
        return sequent;
    }

    /**
     * Returns the result of the problem. If more than one solver have been applied on the problem
     * it computes the result from the results of the solvers. In case that one solver returned a
     * positive result (valid) and another one a negative result (falsifiable) an excpetion is
     * thrown.
     */
    public SMTSolverResult getFinalResult() {
        SMTSolverResult unknown = SMTSolverResult.NO_IDEA;
        SMTSolverResult valid = null;
        SMTSolverResult invalid = null;
        for (SMTSolver solver : solvers) {
            SMTSolverResult solverResult = solver.getFinalResult();
            if (solverResult == null) {
                // do nothing
            } else if (solverResult.isValid() == ThreeValuedTruth.VALID) {
                valid = solverResult;
            } else if (solverResult.isValid() == ThreeValuedTruth.FALSIFIABLE) {
                invalid = solverResult;
            } else {
                unknown = solverResult;
            }
        }
        if (valid != null && invalid != null) {
            throw new IllegalStateException("FATAL ERROR: The results are inconsistent for goal "
                + Objects.requireNonNull(goal, "goal").node().serialNr() + "!");
        }
        if (valid != null) {
            return valid;
        }
        if (invalid != null) {
            return invalid;
        }
        return unknown;
    }

    /**
     * @return the solver that finished this problem
     */
    public @Nullable SMTSolver getSuccessfulSolver() {
        for (SMTSolver solver : solvers) {
            var finalResult = solver.getFinalResult();
            if (finalResult != null
                    && finalResult.isValid() == ThreeValuedTruth.VALID) {
                return solver;
            }
        }
        return null;
    }

    public String getName() {
        return name;
    }

    /* ############# Implementation ############## */

    /**
     * Relates a solver to the problem
     *
     * @param solver
     */
    void addSolver(SMTSolver solver) {
        solvers.add(solver);
    }

    public static JTerm sequentToTerm(Sequent s, Services services) {
        ImmutableList<JTerm> ante = ImmutableList.nil();

        final TermBuilder tb = services.getTermBuilder();
        ante = ante.append(tb.tt());
        for (SequentFormula f : s.antecedent()) {
            ante = ante.append((JTerm) f.formula());
        }

        ImmutableList<JTerm> succ = ImmutableList.nil();
        succ = succ.append(tb.ff());
        for (SequentFormula f : s.succedent()) {
            succ = succ.append((JTerm) f.formula());
        }

        return tb.imp(tb.and(ante), tb.or(succ));

    }


    private JTerm sequentToTerm(Sequent s) {

        ImmutableList<JTerm> ante = ImmutableList.nil();

        final TermBuilder tb =
            Objects.requireNonNull(goal, "goal").proof().getServices().getTermBuilder();
        ante = ante.append(tb.tt());
        for (SequentFormula f : s.antecedent()) {
            ante = ante.append((JTerm) f.formula());
        }

        ImmutableList<JTerm> succ = ImmutableList.nil();
        succ = succ.append(tb.ff());
        for (SequentFormula f : s.succedent()) {
            succ = succ.append((JTerm) f.formula());
        }

        return tb.imp(tb.and(ante), tb.or(succ));

    }

    private JTerm goalToTerm(Goal g) {
        sequent = g.sequent();
        return sequentToTerm(sequent);
    }

}
