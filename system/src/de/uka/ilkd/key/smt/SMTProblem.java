// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

/**
 * Represents a problem that can be passed to a solver. This class was
 * introduced because the SMT module must handle both goals and terms.<br>
 * Each <code>SMTProblem</code> is related to a set of solvers that are used to
 * solve this problem.
 * 
 */
public class SMTProblem {

        private Term term;
        private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();
        private final Goal goal;
        private Sequent sequent;
        private String name = "";

        /* ############# public interface ############# */
        /**
         * Creates out of a proof object several SMT problems. For each open
         * goal a new SMT problem is created.
         */
        public static Collection<SMTProblem> createSMTProblems(Proof proof) {
                LinkedList<SMTProblem> problems = new LinkedList<SMTProblem>();
                for (Goal goal : proof.openGoals()) {
                        problems.add(new SMTProblem(goal));
                }
                return problems;
        }

        /**
         * Returns the term that is related to this problem. If the problem was
         * initialized with a goal, the goal is transformed to the term that can
         * be accessed by this method.
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
                name = "Goal " + goal.node().serialNr();
                term = goalToTerm(goal);
        }

        public Goal getGoal() {
                return goal;
        }

        public Sequent getSequent() {
                return sequent;
        }

        /**
         * Returns the result of the problem. If more than one solver have been
         * applied on the problem it computes the result from the results of the
         * solvers. In case that one solver returned a positive result (valid)
         * and another one a negative result (falsifiable) an excpetion is
         * thrown.
         */
        public SMTSolverResult getFinalResult() {
                SMTSolverResult unknown = SMTSolverResult.NO_IDEA;
                SMTSolverResult valid = null;
                SMTSolverResult invalid = null;
                for (SMTSolver solver : solvers) {
                	    if(solver.getFinalResult() == null){
                	    	// do nothing
                	    }else if (solver.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                                valid = solver.getFinalResult();
                        } else if (solver.getFinalResult().isValid() == ThreeValuedTruth.FALSIFIABLE) {
                                invalid = solver.getFinalResult();
                        } else {
                                unknown = solver.getFinalResult();
                        }
                }
                if (valid != null && invalid != null) {
                        throw new RuntimeException(
                                        "FATAL ERROR: The results are inconsistent!");
                }
                if (valid != null) {
                        return valid;
                }
                if (invalid != null) {
                        return invalid;
                }
                return unknown;
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
