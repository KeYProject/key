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
import java.util.LinkedList;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Case;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.Finally;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
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
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * The macro FinishSymbolicExecutionUntilJionPointMacro continues automatic rule
 * application until a join point is reached (i.e. a point where a JoinRule can
 * be applied) or there is no more modality on the sequent.
 * <p>
 * 
 * This is done by implementing a delegation {@link Strategy} which assigns to
 * any rule application infinite costs if there is no modality on the sequent.
 * 
 * @author Mattias Ulbrich
 * @author Dominic Scheurer
 * @see FinishSymbolicExecutionMacro
 */
public class FinishSymbolicExecutionUntilJoinPointMacro extends
        StrategyProofMacro {

    private HashSet<ProgramElement> blockElems = new HashSet<ProgramElement>();
    private HashSet<JavaBlock> alreadySeen = new HashSet<JavaBlock>();

    private UserInterfaceControl uic = null;

    public FinishSymbolicExecutionUntilJoinPointMacro() {
    }

    public FinishSymbolicExecutionUntilJoinPointMacro(
            HashSet<ProgramElement> blockElems) {
        this.blockElems = blockElems;
    }

    @Override
    public String getName() {
        return "Finish symbolic execution until join point";
    }

    @Override
    public String getCategory() {
        return "Join";
    }

    @Override
    public String getDescription() {
        return "Continue automatic strategy application until a "
                + "join point is reached or there is no more modality in the sequent.";
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
                            .getActiveStatement(JoinRuleUtils.getJavaBlockRecursive(formula
                                    .formula())))) {
                return true;
            }
        }

        return false;
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
                JavaBlock theJavaBlock = JoinRuleUtils.getJavaBlockRecursive(pio.subTerm());
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
                    // would have to do a simplification ourselves before
                    // joining nodes.
                    return true;

                }
            }

            return super.isApprovedApp(app, pio, goal);
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
                        result.addAll(findJoinPoints(body, services));
                    }
                    stmt = stmt.getFirstElement();
                }
            }

            for (int i = 0; i < stmts.size(); i++) {
                SourceElement stmt = stmts.get(i);

                if ((stmt instanceof If || stmt instanceof Try)
                        && i < stmts.size() - 1) {
                    // We have found a reason for a break point (i.e.,
                    // a try or if statement), so let's add the next
                    // statement as a break point.
                    result.add(stmts.get(i + 1));
                }

                if ((stmt instanceof LoopStatement) && i < stmts.size() - 1) {
                    // If a loop statement contains a break, we also
                    // have a potential join point.
                    // Note: The FindBreakVisitor does not take care
                    // of potential nested loops, so there may occur
                    // an early stop in this case.

                    FindBreakVisitor visitor = new FindBreakVisitor(getBodies(
                            stmt).element(), services);
                    visitor.start();
                    if (visitor.containsBreak()) {
                        result.add(stmts.get(i + 1));
                    }
                }
            }

            return result;
        }

        /**
         * Visitor for finding out whether there is a break statement contained
         * in a program element.
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
        };

        /**
         * Returns the bodies for various compound statements like if, try,
         * case, etc. If there is no body, an empty list is returned.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(SourceElement elem) {
            if (elem instanceof If) {
                return getBodies((If) elem);
            }
            else if (elem instanceof Then) {
                return getBodies((Then) elem);
            }
            else if (elem instanceof Else) {
                return getBodies((Else) elem);
            }
            else if (elem instanceof Try) {
                return getBodies((Try) elem);
            }
            else if (elem instanceof Catch) {
                return getBodies((Catch) elem);
            }
            else if (elem instanceof Finally) {
                return getBodies((Finally) elem);
            }
            else if (elem instanceof MethodFrame) {
                return getBodies((MethodFrame) elem);
            }
            else if (elem instanceof Case) {
                return getBodies((Case) elem);
            }
            else if (elem instanceof CatchAllStatement) {
                return getBodies((CatchAllStatement) elem);
            }
            else if (elem instanceof LabeledStatement) {
                return getBodies((LabeledStatement) elem);
            }
            else if (elem instanceof LoopStatement) {
                return getBodies((LoopStatement) elem);
            }
            else if (elem instanceof SynchronizedBlock) {
                return getBodies((SynchronizedBlock) elem);
            }
            else {
                return new LinkedList<StatementBlock>();
            }
        }

        /**
         * Returns the bodies for an If element. NOTE: This includes the bodies
         * for the Then *and* the Else part!
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(If elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            result.addAll(getBodies(elem.getThen()));

            if (elem.getElse() != null) {
                result.addAll(getBodies(elem.getElse()));
            }

            return result;
        }

        /**
         * Returns the body for a Then element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Then elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add((StatementBlock) thenBody);
            }

            return result;
        }

        /**
         * Returns the body for an Else element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Else elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement elseBody = elem.getBody();
            if (elseBody instanceof StatementBlock) {
                result.add((StatementBlock) elseBody);
            }

            return result;
        }

        /**
         * Returns the bodies for a Try element. NOTE: This includes the bodies
         * for Try *and* for the branches!
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Try elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            if (elem instanceof Try) {
                Statement tryBody = elem.getBody();
                if (tryBody instanceof StatementBlock) {
                    result.add((StatementBlock) tryBody);
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
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Catch elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement catchBody = elem.getBody();
            if (catchBody instanceof StatementBlock) {
                result.add((StatementBlock) catchBody);
            }

            return result;
        }

        /**
         * Returns the body for a Finally element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Finally elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement finallyBody = elem.getBody();
            if (finallyBody instanceof StatementBlock) {
                result.add((StatementBlock) finallyBody);
            }

            return result;
        }

        /**
         * Returns the body for a MethodFrame element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(MethodFrame elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement methodFrameBody = elem.getBody();
            if (methodFrameBody instanceof StatementBlock) {
                result.add((StatementBlock) methodFrameBody);
            }

            return result;
        }

        /**
         * Returns the bodies for a Case element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(Case elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

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
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(CatchAllStatement elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement catchBody = elem.getBody();
            if (catchBody instanceof StatementBlock) {
                result.add((StatementBlock) catchBody);
            }

            return result;
        }

        /**
         * Returns the body for a LabeledStatement element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(LabeledStatement elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add((StatementBlock) thenBody);
            }

            return result;
        }

        /**
         * Returns the body for a LoopStatement element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(LoopStatement elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add((StatementBlock) thenBody);
            }

            return result;
        }

        /**
         * Returns the body for a SynchronizedBlock element.
         * 
         * @param elem
         *            The element to return the bodies for.
         * @return The bodies for the given source element.
         */
        private LinkedList<StatementBlock> getBodies(SynchronizedBlock elem) {
            LinkedList<StatementBlock> result = new LinkedList<StatementBlock>();

            Statement thenBody = elem.getBody();
            if (thenBody instanceof StatementBlock) {
                result.add((StatementBlock) thenBody);
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
