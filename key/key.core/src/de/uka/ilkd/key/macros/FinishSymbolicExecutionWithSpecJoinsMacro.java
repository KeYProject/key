// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.macros;

import java.util.HashSet;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * TODO
 * 
 * @author Dominic Scheurer
 * @see FinishSymbolicExecutionMacro
 */
public class FinishSymbolicExecutionWithSpecJoinsMacro extends
        StrategyProofMacro {

    private HashSet<ProgramElement> blockElems = new HashSet<ProgramElement>();
    private HashSet<JavaBlock> alreadySeen = new HashSet<JavaBlock>();

    private UserInterfaceControl uic = null;

    public FinishSymbolicExecutionWithSpecJoinsMacro() {
    }

    public FinishSymbolicExecutionWithSpecJoinsMacro(
            HashSet<ProgramElement> blockElems) {
        this.blockElems = blockElems;
    }

    @Override
    public String getName() {
        return "Finish symbolic execution with join specifications";
    }

    @Override
    public String getDescription() {
        return "Continue automatic strategy application and take join procedures "
                + "specified in block contracts into account.";
    }

    /**
     * Returns true iff there is a modality in the sequent of the given node.
     * 
     * @param node
     *            Node to check.
     * @return True iff there is a modality in the sequent of the given node.
     */
    private static boolean hasModality(Node node) {
        Sequent sequent = node.sequent();
        for (SequentFormula sequentFormula : sequent) {
            if (hasModality(sequentFormula.formula())) {
                return true;
            }
        }

        return false;
    }

    /**
     * Recursive check for existence of modality.
     * 
     * @param term
     *            The term to check.
     * @return True iff there is a modality in the sequent of the given term.
     */
    private static boolean hasModality(Term term) {
        if (term.containsLabel(ParameterlessTermLabel.SELF_COMPOSITION_LABEL)) {
            // ignore self composition terms
            return false;
        }

        if (term.op() instanceof Modality) {
            return true;
        }

        for (Term sub : term.subs()) {
            if (hasModality(sub)) {
                return true;
            }
        }

        return false;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
            Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc,
            ProverTaskListener listener) throws InterruptedException {
        this.uic = uic;
        return super.applyTo(uic, proof, goals, posInOcc, listener);
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        // Need to clear the data structures since no new instance of this
        // macro is created across multiple calls, so sometimes it would have
        // no effect in a successive call.
        blockElems.clear();
        alreadySeen.clear();

        return new FilterSymbexStrategy(proof.getActiveStrategy());
    }

    @Override
    protected void doPostProcessing(Proof proof) {
        // This hack was introduced since in a "while loop with break"
        // I discovered that the execution stopped early, that is three
        // automatic steps before a join would be possible.
        // So we do single automatic steps until our break point
        // vanishes; then we undo until the break point is there again.

        for (Goal goal : proof.openEnabledGoals()) {

            if (!hasBreakPoint(goal.sequent().succedent())) {
                continue;
            }

            Node lastNode = goal.node();
            do {
                try {
                    // Do single proof step
                    new OneStepProofMacro().applyTo(uic, goal.node(), null,
                            DUMMY_PROVER_TASK_LISTENER); // TODO Change
                }
                catch (InterruptedException e) {
                }
                catch (Exception e) {
                }

                // We want no splits, but the proof must have changed
                if (lastNode.childrenCount() == 1) {
                    lastNode = lastNode.child(0);
                }
                else {
                    break;
                }
            }
            while (hasBreakPoint(goal.sequent().succedent()));

            // Undo until a break condition is the first active statement again.
            while (!hasBreakPoint(lastNode.sequent().succedent())) {
                lastNode = lastNode.parent();
                proof.pruneProof(lastNode);
            }

        }
    }

    /**
     * Dummy ProverTaskListener.
     */
    private static final ProverTaskListener DUMMY_PROVER_TASK_LISTENER = new ProverTaskListener() {
        @Override
        public void taskProgress(int position) {
        }

        @Override
        public void taskStarted(TaskStartedInfo info) {
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
        }
    };

    /**
     * @param succedent
     *            Succedent of a sequent.
     * @return true iff the given succedent has one formula with a break point
     *         statement.
     */
    private boolean hasBreakPoint(Semisequent succedent) {
        for (SequentFormula formula : succedent.asList()) {
            if (blockElems
                    .contains(JavaTools
                            .getActiveStatement(getJavaBlockRecursive(formula
                                    .formula())))) {
                return true;
            }
        }

        return false;
    }

    /**
     * Returns the first Java block in the given term that can be found by
     * recursive search, or the empty block if there is no non-empty Java block
     * in the term.
     * 
     * @param term
     *            The term to extract Java blocks for.
     * @return The first Java block in the given term or the empty block if
     *         there is no non-empty Java block.
     */
    private static JavaBlock getJavaBlockRecursive(Term term) {
        if (term.subs().size() == 0 || !term.javaBlock().isEmpty()) {
            return term.javaBlock();
        }
        else {
            for (Term sub : term.subs()) {
                JavaBlock subJavaBlock = getJavaBlockRecursive(sub);
                if (!subJavaBlock.isEmpty()) {
                    return subJavaBlock;
                }
            }
            return JavaBlock.EMPTY_JAVABLOCK;
        }
    }

    /**
     * The Class FilterSymbexStrategy is a special strategy assigning to any
     * rule infinite costs if the goal has no modality or if a join point is
     * reached.
     */
    private class FilterSymbexStrategy extends FilterStrategy {

        private final Name NAME = new Name(
                FilterSymbexStrategy.class.getSimpleName());

        public FilterSymbexStrategy(Strategy delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if (!hasModality(goal.node())) {
                return false;
            }

            if (hasBreakPoint(goal.sequent().succedent())) {
                return false;
            }

            if (pio != null) {
                JavaBlock theJavaBlock = getJavaBlockRecursive(pio.subTerm());
                SourceElement activeStmt = JavaTools
                        .getActiveStatement(theJavaBlock);

                if (!(theJavaBlock.program() instanceof StatementBlock)
                        || (alreadySeen.contains(theJavaBlock) && !blockElems
                                .contains(activeStmt))) {
                    // For sake of efficiency: Do not treat the same
                    // statement block multiple times. However, we have
                    // to consider it if it is a break point, of course.
                    return super.isApprovedApp(app, pio, goal);
                }
                else if (!theJavaBlock.equals(JavaBlock.EMPTY_JAVABLOCK)) {
                    alreadySeen.add(theJavaBlock);
                }

                // Find break points
                blockElems.addAll(findJoinPoints((StatementBlock) theJavaBlock
                        .program(), goal.proof().getServices()));

                if (app.rule().name().toString()
                        .equals("One Step Simplification")) {

                    // We allow One Step Simplification, otherwise we sometimes
                    // would
                    // have to do a simplification ourselves before joining
                    // nodes.
                    return true;

                }
                else if (blockElems.contains((ProgramElement) activeStmt)) {
                    // TODO: This check could be superfluous, since we already
                    // check whether there is a break point at the beginning
                    // of this method.
                    return false;

                }
            }

            return super.isApprovedApp(app, pio, goal);
        }

        /**
         * TODO: Document.
         *
         * @param sb
         * @return
         */
        private StatementBlock stripMethodFrame(final StatementBlock sb) {
            if (sb.getBody().get(0) instanceof Try) {
                Try theTry = (Try) sb.getBody().get(0);
                if (theTry.getBody().getBody().get(0) instanceof MethodFrame) {
                    MethodFrame theMethodFrame = (MethodFrame) theTry.getBody()
                            .getBody().get(0);
                    return theMethodFrame.getBody();
                }
            }

            return sb;
        }

        /**
         * Returns a set of join points for the given statement block. A join
         * point is the statement in a program directly after an if-then-else or
         * a try-catch-finally block.
         * 
         * @param toSearch
         *            The statement block to search for join points.
         * @return A set of join points for the given statement block.
         */
        private HashSet<ProgramElement> findJoinPoints(StatementBlock toSearch,
                Services services) {
            HashSet<ProgramElement> result = new HashSet<ProgramElement>();

            if (toSearch.isEmpty()) {
                return result;
            }

            StatementBlock blockWithoutMethodFrame = stripMethodFrame(toSearch);
            Statement firstElem = blockWithoutMethodFrame.getBody().get(0);
            if (firstElem instanceof StatementBlock
                    && !services.getSpecificationRepository()
                            .getBlockContracts((StatementBlock) firstElem)
                            .isEmpty()) {
                if (blockWithoutMethodFrame.getBody().size() > 1) {
                    blockElems.add(blockWithoutMethodFrame.getBody().get(1));
                }
            }

            return result;
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }

}
