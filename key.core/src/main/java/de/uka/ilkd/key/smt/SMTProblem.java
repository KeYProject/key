/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Represents a problem that can be passed to a solver. This class was introduced because the SMT
 * module must handle both goals and terms.<br>
 * Each <code>SMTProblem</code> is related to a set of solvers that are used to solve this problem.
 *
 */
public class SMTProblem {

    private final Term term;
    private final Collection<SMTSolver> solvers = new LinkedList<>();
    private final Goal goal;
    private final Node node;
    private Sequent sequent;
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
    public Term getTerm() {
        return term;
    }

    /** Returns the solvers that are related to the problem */
    public Collection<SMTSolver> getSolvers() {
        return solvers;
    }

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

    public SMTProblem(Term t) {
        this.goal = null;
        this.node = null;
        name = "Term " + t.toString();
        this.term = t;
    }

    public Goal getGoal() {
        return goal;
    }

    public Node getNode() {
        return node;
    }

    public Sequent getSequent() {
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
            if (solver.getFinalResult() == null) {
                // do nothing
            } else if (solver.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                valid = solver.getFinalResult();
            } else if (solver.getFinalResult().isValid() == ThreeValuedTruth.FALSIFIABLE) {
                invalid = solver.getFinalResult();
            } else {
                unknown = solver.getFinalResult();
            }
        }
        if (valid != null && invalid != null) {
            throw new IllegalStateException("FATAL ERROR: The results are inconsistent for goal "
                + goal.node().serialNr() + "!");
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
    public SMTSolver getSuccessfulSolver() {
        for (SMTSolver solver : solvers) {
            if (solver.getFinalResult() != null
                    && solver.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
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

    public static Term sequentToTerm(Sequent s, Services services) {

        ImmutableList<Term> ante = ImmutableSLList.nil();

        final TermBuilder tb = services.getTermBuilder();
        ante = ante.append(tb.tt());
        for (SequentFormula f : s.antecedent()) {
            ante = ante.append(f.formula());
        }

        ImmutableList<Term> succ = ImmutableSLList.nil();
        succ = succ.append(tb.ff());
        for (SequentFormula f : s.succedent()) {
            succ = succ.append(f.formula());
        }

        return tb.imp(tb.and(ante), tb.or(succ));

    }


    private Term sequentToTerm(Sequent s) {

        ImmutableList<Term> ante = ImmutableSLList.nil();

        final TermBuilder tb = goal.proof().getServices().getTermBuilder();
        ante = ante.append(tb.tt());
        for (SequentFormula f : s.antecedent()) {
            ante = ante.append(f.formula());
        }

        ImmutableList<Term> succ = ImmutableSLList.nil();
        succ = succ.append(tb.ff());
        for (SequentFormula f : s.succedent()) {
            succ = succ.append(f.formula());
        }

        return tb.imp(tb.and(ante), tb.or(succ));

    }

    private Term goalToTerm(Goal g) {
        sequent = g.sequent();
        return sequentToTerm(sequent);
    }

}
