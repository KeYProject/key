/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.HashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * The macro FinishSymbolicExecutionUntilJionPointMacro continues automatic rule application until a
 * merge point is reached (i.e. a point where a {@link MergeRule} can be applied) or there is no
 * more modality on the sequent.
 * <p>
 *
 * This is done by implementing a delegation {@link Strategy} which assigns to any rule application
 * infinite costs if there is no modality on the sequent.
 *
 * @author Mattias Ulbrich
 * @author Dominic Scheurer
 * @see FinishSymbolicExecutionMacro
 */
public class FinishSymbolicExecutionUntilMergePointMacro extends StrategyProofMacro {

    private HashSet<ProgramElement> blockElems = new HashSet<>();
    private final HashSet<JavaBlock> alreadySeen = new HashSet<>();

    private UserInterfaceControl uic = null;

    public FinishSymbolicExecutionUntilMergePointMacro() {
    }

    public FinishSymbolicExecutionUntilMergePointMacro(HashSet<ProgramElement> blockElems) {
        this.blockElems = blockElems;
    }

    @Override
    public String getName() {
        return "Finish symbolic execution until merge point";
    }

    @Override
    public String getCategory() {
        return "Merge";
    }

    @Override
    public String getDescription() {
        return "Continue automatic strategy application until a "
            + "merge point is reached or there is no more modality in the sequent.";
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws InterruptedException {
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
        // automatic steps before a merge would be possible.
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
                } catch (Exception e) {
                }

                // We want no splits, but the proof must have changed
                if (lastNode.childrenCount() == 1) {
                    lastNode = lastNode.child(0);
                } else {
                    break;
                }
            } while (hasBreakPoint(goal.sequent().succedent()));

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
     * @param succedent Succedent of a sequent.
     * @return true iff the given succedent has one formula with a break point statement.
     */
    private boolean hasBreakPoint(Semisequent succedent) {
        for (SequentFormula formula : succedent.asList()) {
            if (blockElems.contains(JavaTools
                    .getActiveStatement(MergeRuleUtils.getJavaBlockRecursive(formula.formula())))) {
                return true;
            }
        }

        return false;
    }

    /**
     * The Class FilterSymbexStrategy is a special strategy assigning to any rule infinite costs if
     * the goal has no modality or if a merge point is reached.
     */
    private class FilterSymbexStrategy extends FilterStrategy {

        private final Name NAME = new Name(FilterSymbexStrategy.class.getSimpleName());
        /** the modality cache used by this strategy */
        private final ModalityCache modalityCache = new ModalityCache();

        public FilterSymbexStrategy(Strategy delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if (!modalityCache.hasModality(goal.node().sequent())) {
                return false;
            }

            if (FinishSymbolicExecutionMacro.isForbiddenRule(app.rule())) {
                return false;
            }

            if (hasBreakPoint(goal.sequent().succedent())) {
                return false;
            }

            if (pio != null) {
                JavaBlock theJavaBlock = MergeRuleUtils.getJavaBlockRecursive(pio.subTerm());
                SourceElement activeStmt = JavaTools.getActiveStatement(theJavaBlock);

                if (!(theJavaBlock.program() instanceof StatementBlock)
                        || (alreadySeen.contains(theJavaBlock)
                                && !blockElems.contains(activeStmt))) {
                    // For sake of efficiency: Do not treat the same
                    // statement block multiple times. However, we have
                    // to consider it if it is a break point, of course.
                    return super.isApprovedApp(app, pio, goal);
                } else if (!theJavaBlock.equals(JavaBlock.EMPTY_JAVABLOCK)) {
                    alreadySeen.add(theJavaBlock);
                }

                // Find break points
                blockElems.addAll(findMergePoints((StatementBlock) theJavaBlock.program(),
                    goal.proof().getServices()));

                if (app.rule().name().toString().equals("One Step Simplification")) {

                    // We allow One Step Simplification, otherwise we sometimes
                    // would have to do a simplification ourselves before
                    // merging nodes.
                    return true;

                }
            }

            return super.isApprovedApp(app, pio, goal);
        }

        /**
         * Returns a set of merge points for the given statement block. A merge point is the
         * statement in a program directly after an if-then-else or a try-catch-finally block.
         *
         * @param toSearch The statement block to search for merge points.
         * @return A set of merge points for the given statement block.
         */
        private HashSet<ProgramElement> findMergePoints(StatementBlock toSearch,
                Services services) {
            HashSet<ProgramElement> result = new HashSet<>();
            ImmutableArray<? extends Statement> stmts = toSearch.getBody();

            if (stmts.size() > 0) {
                // Recursive step: Go deeper in the first statement
                // (the other statements will be objects to future
                // rule applications) and try to find breakpoints.
                // Essential if the first statement is a try, if or
                // method frame.
                SourceElement stmt = stmts.get(0);
                while (!stmt.getFirstElement().equals(stmt)) {
                    for (StatementBlock body : getBodies(stmt)) {
                        result.addAll(findMergePoints(body, services));
                    }
                    stmt = stmt.getFirstElement();
                }
            }

            for (int i = 0; i < stmts.size(); i++) {
                SourceElement stmt = stmts.get(i);

                if ((stmt instanceof If || stmt instanceof Try) && i < stmts.size() - 1) {
                    // We have found a reason for a break point (i.e.,
                    // a try or if statement), so let's add the next
                    // statement as a break point.
                    result.add(stmts.get(i + 1));
                }

                if ((stmt instanceof LoopStatement) && i < stmts.size() - 1) {
                    // If a loop statement contains a break, we also
                    // have a potential merge point.
                    // Note: The FindBreakVisitor does not take care
                    // of potential nested loops, so there may occur
                    // an early stop in this case.

                    FindBreakVisitor visitor =
                        new FindBreakVisitor(getBodies(stmt).element(), services);
                    visitor.start();
                    if (visitor.containsBreak()) {
                        result.add(stmts.get(i + 1));
                    }
                }
            }

            return result;
        }

        /**
         * Visitor for finding out whether there is a break statement contained in a program
         * element.
         */
        private class FindBreakVisitor extends JavaASTVisitor {
            private boolean containsBreak = false;

            public FindBreakVisitor(ProgramElement root, Services services) {
                super(root, services);
            }

            /**
             * @return true iff the visitor did find a break.
             */
            public boolean containsBreak() {
                return containsBreak;
            }

            @Override
            protected void doDefaultAction(SourceElement node) {
            }

            @Override
            public void performActionOnBreak(Break x) {
                containsBreak = true;
            }
        }

        /**
         * Returns the bodies for various compound statements like if, try, case, etc. If there is
         * no body, an empty list is returned.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(SourceElement elem) {
            if (elem instanceof If) {
                return getBodies((If) elem);
            } else if (elem instanceof Then) {
                return getBodies((Then) elem);
            } else if (elem instanceof Else) {
                return getBodies((Else) elem);
            } else if (elem instanceof Try) {
                return getBodies((Try) elem);
            } else if (elem instanceof Catch) {
                return getBodies((Catch) elem);
            } else if (elem instanceof Finally) {
                return getBodies((Finally) elem);
            } else if (elem instanceof MethodFrame) {
                return getBodies((MethodFrame) elem);
            } else if (elem instanceof Case) {
                return getBodies((Case) elem);
            } else if (elem instanceof CatchAllStatement) {
                return getBodies((CatchAllStatement) elem);
            } else if (elem instanceof LabeledStatement) {
                return getBodies((LabeledStatement) elem);
            } else if (elem instanceof LoopStatement) {
                return getBodies((LoopStatement) elem);
            } else if (elem instanceof SynchronizedBlock) {
                return getBodies((SynchronizedBlock) elem);
            } else {
                return new LinkedList<>();
            }
        }

        /**
         * Returns the bodies for an If element. NOTE: This includes the bodies for the Then *and*
         * the Else part!
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(If elem) {

            LinkedList<StatementBlock> result = new LinkedList<>(getBodies(elem.getThen()));

            if (elem.getElse() != null) {
                result.addAll(getBodies(elem.getElse()));
            }

            return result;
        }

        /**
         * Returns the body for a Then element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Then elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            Statement thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add((StatementBlock) thenBody);
            }

            return result;
        }

        /**
         * Returns the body for an Else element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Else elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            Statement elseBody = elem.getBody();
            if (elseBody instanceof StatementBlock) {
                result.add((StatementBlock) elseBody);
            }

            return result;
        }

        /**
         * Returns the bodies for a Try element. NOTE: This includes the bodies for Try *and* for
         * the branches!
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Try elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            if (elem instanceof Try) {
                StatementBlock tryBody = elem.getBody();
                if (tryBody instanceof StatementBlock) {
                    result.add(tryBody);
                }

                ImmutableArray<Branch> branches = elem.getBranchList();
                for (Branch branch : branches) {
                    result.addAll(getBodies(branch));
                }
            }

            return result;
        }

        /**
         * Returns the body for a Catch element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Catch elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            StatementBlock catchBody = elem.getBody();
            if (catchBody instanceof StatementBlock) {
                result.add(catchBody);
            }

            return result;
        }

        /**
         * Returns the body for a Finally element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Finally elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            StatementBlock finallyBody = elem.getBody();
            if (finallyBody instanceof StatementBlock) {
                result.add(finallyBody);
            }

            return result;
        }

        /**
         * Returns the body for a MethodFrame element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(MethodFrame elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            StatementBlock methodFrameBody = elem.getBody();
            if (methodFrameBody instanceof StatementBlock) {
                result.add(methodFrameBody);
            }

            return result;
        }

        /**
         * Returns the bodies for a Case element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Case elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            ImmutableArray<Statement> caseBodies = elem.getBody();
            for (Statement body : caseBodies) {
                if (body instanceof StatementBlock) {
                    result.add((StatementBlock) body);
                }
            }

            return result;
        }

        /**
         * Returns the body for a CatchAllStatement element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(CatchAllStatement elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            Statement catchBody = elem.getBody();
            if (catchBody instanceof StatementBlock) {
                result.add((StatementBlock) catchBody);
            }

            return result;
        }

        /**
         * Returns the body for a LabeledStatement element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(LabeledStatement elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            Statement thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add((StatementBlock) thenBody);
            }

            return result;
        }

        /**
         * Returns the body for a LoopStatement element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(LoopStatement elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            Statement thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add((StatementBlock) thenBody);
            }

            return result;
        }

        /**
         * Returns the body for a SynchronizedBlock element.
         *
         * @param elem The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(SynchronizedBlock elem) {
            LinkedList<StatementBlock> result = new LinkedList<>();

            StatementBlock thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add(thenBody);
            }

            return result;
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            // TODO Auto-generated method stub
            return false;
        }

    }

}
