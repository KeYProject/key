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

import java.util.HashMap;
import java.util.HashSet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.join.JoinRule;
import de.uka.ilkd.key.rule.join.JoinRuleBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedRuleApplicationManager;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * Finishes symbolic execution while taking JML join specifications into
 * account: Branches are joined at defined points during the execution.
 *
 * @author Dominic Scheurer
 * @see FinishSymbolicExecutionMacro
 */
public class FinishSymbolicExecutionWithSpecJoinsMacro extends
        AbstractProofMacro {

    @Override
    public String getName() {
        return "Finish symbolic execution with join specifications";
    }

    @Override
    public String getCategory() {
        return "Join";
    }

    @Override
    public String getDescription() {
        return "Continue automatic strategy application and take join procedures "
                + "specified in block contracts into account.";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            PosInOccurrence posInOcc) {
        return goals != null && !goals.isEmpty();
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
            Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc,
            ProverTaskListener listener) throws InterruptedException {

        if (goals == null || goals.isEmpty()) {
            // Should not happen, because in this case canApplyTo returns false
            return null;
        }

        final IGoalChooser goalChooser = proof.getInitConfig().getProfile()
                .getSelectedGoalChooserBuilder().create();
        final ApplyStrategy applyStrategy = new ApplyStrategy(goalChooser);
        final ImmutableList<Goal> ignoredOpenGoals = setDifference(
                proof.openGoals(), goals);

        // The observer to handle the progress bar
        final ProofMacroListener pml = new ProgressBarListener(
                goals.size(), getMaxSteps(proof), listener);
        applyStrategy.addProverTaskObserver(pml);

        // Add a focus manager if there is a focus
        if (posInOcc != null && goals != null) {
            AutomatedRuleApplicationManager realManager = null;
            FocussedRuleApplicationManager manager = null;
            for (Goal goal : goals) {
                realManager = goal.getRuleAppManager();
                realManager.clearCache();
                manager = new FocussedRuleApplicationManager(realManager, goal,
                        posInOcc);
                goal.setRuleAppManager(manager);
            }
        }

        // Set the FilterSymbexStrategy as new strategy.
        Strategy oldStrategy = proof.getActiveStrategy();
        FilterSymbexStrategy strategy = new FilterSymbexStrategy(
                proof.getActiveStrategy());
        proof.setActiveStrategy(strategy);

        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals,
                proof);
        try {
            // Run symbolic execution and join until the execution finishes
            // with no join applicable. Whenever the FilterSymbexStrategy
            // finds a join point, it stops the execution such that we can
            // apply the join at this place.
            boolean joined;
            do {
                joined = false;
                applyStrategy.start(proof, goals);
                synchronized (applyStrategy) { // wait for applyStrategy to
                                               // finish its last rule
                                               // application
                    if (applyStrategy.hasBeenInterrupted()) { // reraise
                                                              // interrupted
                                                              // exception if
                                                              // necessary
                        throw new InterruptedException();
                    }
                }

                Pair<Goal, JoinRuleBuiltInRuleApp> joinInfo = strategy
                        .getAndResetJoinInformation();
                if (joinInfo != null) {
                    // We are at a join point: Execute the join.
                    joinInfo.first.apply(joinInfo.second);
                    joined = true;
                }
            }
            while (joined);
        }
        finally {
            // This resets the proof strategy and the managers after the
            // automation has run.
            for (final Goal openGoal : proof.openGoals()) {
                AutomatedRuleApplicationManager manager = openGoal
                        .getRuleAppManager();

                // Touch the manager only if necessary.
                if (manager.getDelegate() != null) {
                    while (manager.getDelegate() != null) {
                        manager = manager.getDelegate();
                    }
                    manager.clearCache();
                    openGoal.setRuleAppManager(manager);
                }
            }

            final ImmutableList<Goal> resultingGoals = setDifference(
                    proof.openGoals(), ignoredOpenGoals);
            info = new ProofMacroFinishedInfo(this, resultingGoals);
            proof.setActiveStrategy(oldStrategy);
            applyStrategy.removeProverTaskObserver(pml);
        }
        return info;
    }

    /**
     * Computes the set difference of the two given lists.
     *
     * @param list1
     *            First list.
     * @param list2
     *            Second list.
     * @return A list containing all elements that are in the first but not in
     *         the second list.
     */
    private static <T> ImmutableList<T> setDifference(ImmutableList<T> list1,
            ImmutableList<T> list2) {
        ImmutableList<T> difference = list1;
        for (T elem : list2) {
            difference = difference.removeFirst(elem);
        }
        return difference;
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

    /**
     * @param block
     *            The statement block which is assumed to wrap another block by
     *            a method frame.
     * @return The second element within the Java block inside the method frame
     *         of the given block, or null if no such element exists.
     */
    private Statement getSecondStatementOfMethodFrameBlock(StatementBlock block, Services services) {
        return getNthStatementOfMethodFrameBlock(block, 1, services);
    }

    /**
     * @param block
     *            The statement block which is assumed to wrap another block by
     *            a method frame.
     * @param n
     *            Specification of the element to obtain.
     * @return The n-th element within the Java block inside the method frame of
     *         the given block, or null if no such element exists.
     */
    private Statement getNthStatementOfMethodFrameBlock(StatementBlock block,
            int n, Services services) {
        StatementBlock blockWithoutMethodFrame = stripMethodFrame(block, services);

        if (blockWithoutMethodFrame.getBody().size() < n + 1) {
            return null;
        }

        return blockWithoutMethodFrame.getBody().get(n);
    }

    /**
     * Removes the <code>try { method-frame { ... }}</code> parts from the given
     * statement block, i.e. returns the inner code. If there is nothing to
     * remove, the original block is returned.
     *
     * @param sb
     *            The statement block to remove the try/method-frame parts from.
     * @return The stripped inner statement block or the original argument, if
     *         the removal was not applicable.
     */
    private StatementBlock stripMethodFrame(final StatementBlock sb,
            final Services services) {
        if (sb.isEmpty()) {
            return sb;
        }

        try {
            final StatementBlock innerMostMethodFrameBody =
                    JavaTools.getInnermostMethodFrame(
                            JavaBlock.createJavaBlock(sb), services).getBody();

            if (innerMostMethodFrameBody.getBody().size() > 0 &&
                    innerMostMethodFrameBody.getBody().get(0) instanceof Try) {
                return ((Try) innerMostMethodFrameBody.getBody().get(0)).getBody();
            } else {
                return innerMostMethodFrameBody;
            }
        }
        catch (NullPointerException e) {
            // This may happen if the statement has no method frame.
            // TODO: Should probably replace this by an explicit check.
        }

        return sb;
    }

    /**
     * The Class FilterSymbexStrategy is a special strategy assigning to any
     * rule infinite costs if the goal has no modality or if a join point is
     * reached.
     */
    private class FilterSymbexStrategy extends FilterStrategy {

        private final Name NAME = new Name(
                FilterSymbexStrategy.class.getSimpleName());

        private boolean enforceJoin = false;

        private Pair<Goal, JoinRuleBuiltInRuleApp> joinInformation = null;

        private HashSet<ProgramElement> breakpoints = new HashSet<ProgramElement>();
        private HashMap<ProgramElement, Node> commonParents = new HashMap<ProgramElement, Node>();
        private HashMap<ProgramElement, BlockContract> joinContracts = new HashMap<ProgramElement, BlockContract>();
        private HashSet<Goal> stoppedGoals = new HashSet<Goal>();
        private HashSet<JavaBlock> alreadySeen = new HashSet<JavaBlock>();

        /**
         * Returns the information for a join to apply if applicable, or null if
         * there is no join to execute. Every call reset the join information,
         * such that the strategy can continue.
         *
         * @return The information for a join to apply if applicable, or null if
         *         there is no join to execute.
         */
        public Pair<Goal, JoinRuleBuiltInRuleApp> getAndResetJoinInformation() {
            final Pair<Goal, JoinRuleBuiltInRuleApp> oldJoinInformation = joinInformation;
            enforceJoin = false;
            joinInformation = null;
            return oldJoinInformation;
        }

        /**
         * Creates a new FilterSymbexStrategy based on the given delegate.
         *
         * @param delegate
         *            The strategy to wrap.
         */
        public FilterSymbexStrategy(Strategy delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if (enforceJoin || stoppedGoals.contains(goal)
                    || !hasModality(goal.node())) {
                return false;
            }

            if (pio != null) {
                JavaBlock theJavaBlock = JoinRuleUtils.getJavaBlockRecursive(pio.subTerm());
                SourceElement activeStmt = JavaTools
                        .getActiveStatement(theJavaBlock);

                if (!(theJavaBlock.program() instanceof StatementBlock)
                        || (alreadySeen.contains(theJavaBlock) && !breakpoints
                                .contains(activeStmt))) {
                    // For sake of efficiency: Do not treat the same
                    // statement block multiple times. However, we have
                    // to consider it if it is a break point, of course.
                    return super.isApprovedApp(app, pio, goal);
                }
                else if (!theJavaBlock.equals(JavaBlock.EMPTY_JAVABLOCK)) {
                    alreadySeen.add(theJavaBlock);

                    // Find break points
                    breakpoints.addAll(findJoinPoints(
                            (StatementBlock) theJavaBlock.program(), goal));

                    Statement breakpoint;
                    if ((breakpoint = getBreakPoint(goal.sequent().succedent(), goal.proof().getServices())) != null) {
                        final ImmutableList<Goal> subtreeGoals = goal.proof()
                                .getSubtreeEnabledGoals(
                                        commonParents.get(breakpoint)).removeFirst(goal);

                        boolean allStopped = true;
                        int nrCandidates = 0;
                        for (Goal subGoal : subtreeGoals) {
                            if (!subGoal.isLinked()
                                    && hasBreakPoint(subGoal.sequent().succedent(), goal.proof().getServices(), breakpoint)) {
                                allStopped = allStopped
                                        && stoppedGoals.contains(subGoal);
                                nrCandidates++;
                            }
                        }

                        if (allStopped && nrCandidates > 0) {
                            // We stopped all Goals potentially participating in
                            // the join; now we collect the information about
                            // the join. After a successful join app
                            // initialization, we do not allow any other rule
                            // applications (realized by setting enforceJoin to
                            // true).

                            final JoinRule joinRule = JoinRule.INSTANCE;

                            final Node joinNode = goal.node();
                            final PosInOccurrence joinPio = getPioForBreakpoint(
                                    breakpoint, goal.sequent());
                            final JoinRuleBuiltInRuleApp joinApp = (JoinRuleBuiltInRuleApp) joinRule
                                    .createApp(joinPio, goal.proof()
                                            .getServices());

                            {
                                // Consider only the partners below the common
                                // parent node. Otherwise, we obtain
                                // behavior that may be hard to understand.
                                ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                                        .findPotentialJoinPartners(goal,
                                                joinPio,
                                                commonParents.get(breakpoint));

                                joinApp.setJoinPartners(joinPartners);
                                joinApp.setConcreteRule(joinContracts.get(
                                        breakpoint).getJoinProcedure());
                                joinApp.setJoinNode(joinNode);
                            }

                            for (Goal subgoal : subtreeGoals) {
                                stoppedGoals.remove(subgoal);
                            }
                            breakpoints.remove(breakpoint);
                            commonParents.remove(breakpoint);

                            if (joinApp.getJoinPartners().isEmpty()) {
                                // This is obviously not a real join point: May happen
                                // in certain more complicated scenarios. Stop trying to
                                // join at this point.
                                return super.isApprovedApp(app, pio, goal);
                            } else {
                                joinInformation = new Pair<Goal, JoinRuleBuiltInRuleApp>(
                                        goal, joinApp);
                                enforceJoin = true;
                            }
                        }
                        else {
                            stoppedGoals.add(goal);
                        }

                        return false;
                    }

                    if (app.rule().name().toString()
                            .equals("One Step Simplification")) {

                        // We allow One Step Simplification, otherwise we
                        // sometimes would have to do a simplification ourselves
                        // before joining nodes.
                        return true;

                    }
                }
            }

            return super.isApprovedApp(app, pio, goal);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

        /**
         * Returns the {@link PosInOccurrence} for the given breakpoint
         * statement inside the given sequent, or null if the statement does not
         * exist within the sequent. The returned {@link PosInOccurrence} is the
         * top level formula inside the sequent containing the breakpoint
         * statement.
         *
         * @param breakpoint
         *            The statement to locate inside the sequent.
         * @param sequent
         *            The sequent to find the statement in.
         * @return The top level formula inside the sequent containing the
         *         breakpoint statement.
         */
        private PosInOccurrence getPioForBreakpoint(Statement breakpoint,
                Sequent sequent) {
            Semisequent succedent = sequent.succedent();

            for (SequentFormula formula : succedent) {
                SourceElement activeStmt = JavaTools
                        .getActiveStatement(JoinRuleUtils.getJavaBlockRecursive(formula
                                .formula()));

                if (activeStmt != null
                        && ((Statement) activeStmt).equals(breakpoint)) {
                    return new PosInOccurrence(formula,
                            PosInTerm.getTopLevel(), false);
                }
            }

            return null;
        }

        /**
         * Returns a set of join points for the given statement block. Join
         * points are directly registered once they are found.
         *
         * @param toSearch
         *            The statement block to search for join points.
         * @param goal
         *            The goal corresponding to the statement block.
         * @return A set of join points for the given statement block.
         */
        private HashSet<ProgramElement> findJoinPoints(
                final StatementBlock toSearch, final Goal goal) {
            final Services services = goal.proof().getServices();
            final HashSet<ProgramElement> result = new HashSet<ProgramElement>();

            if (toSearch.isEmpty()) {
                return result;
            }

            final Pair<BlockContract, Statement> contractAndBreakpoint = getBlockContractFor(
                    stripMethodFrame(toSearch, services), services);
            if (contractAndBreakpoint != null) {
                final Statement breakpoint = contractAndBreakpoint.second;
                if (breakpoint != null) {
                    breakpoints.add(breakpoint);
                    commonParents.put(breakpoint, goal.node());
                    joinContracts.put(breakpoint, contractAndBreakpoint.first);
                }
            }

            return result;
        }

        /**
         * Obtains the pair of block contract containing a join specification
         * and the corresponding breakpoint, if any, for the given statement. If
         * there is no such contract, null is returned.
         *
         * @param stmt
         *            Statement to find a contract and breakpoint for. This
         *            should be the whole "program counter", i.e. the next
         *            statement that will be the breakpoint should also be
         *            included.
         * @param services
         *            The services object.
         * @return If any, a join block contract and corresponding break point
         *         for the given statement; null otherwise.
         */
        private Pair<BlockContract, Statement> getBlockContractFor(
                Statement stmt, Services services) {
            Statement breakpoint = null;

            while (stmt instanceof StatementBlock
                    && !((StatementBlock) stmt).isEmpty()) {
                ImmutableSet<BlockContract> contracts;
                if (!(contracts = services.getSpecificationRepository()
                        .getBlockContracts((StatementBlock) stmt)).isEmpty()) {
                    return contracts.iterator().next().hasJoinProcedure() ? new Pair<BlockContract, Statement>(
                            contracts.iterator().next(), breakpoint) : null;
                }

                breakpoint = getSecondStatementOfMethodFrameBlock((StatementBlock) stmt, services);
                if (breakpoint instanceof StatementBlock) {
                    breakpoint = (Statement) JavaTools
                            .getActiveStatement(JavaBlock
                                    .createJavaBlock(((StatementBlock) breakpoint)));
                }

                stmt = (Statement) stmt.getFirstElementIncludingBlocks();
            }

            return null;
        }

        /**
         * @param succedent
         *            Succedent of a sequent.
         * @return A Statement (the registered breakpoint) iff the given
         *         succedent has one formula starting with a break point
         *         statement, else null;
         */
        private Statement getBreakPoint(Semisequent succedent, Services services) {
            for (SequentFormula formula : succedent.asList()) {
                JavaBlock javaBlock = JoinRuleUtils.getJavaBlockRecursive(
                        formula.formula());

                StatementBlock blockWithoutMethodFrame = stripMethodFrame((StatementBlock) javaBlock.program(), services);

                if (blockWithoutMethodFrame.isEmpty()) {
                    continue;
                }

                SourceElement activeStatement = JavaTools
                        .getActiveStatement(javaBlock);
                if (activeStatement instanceof Statement
                        && breakpoints.contains((Statement) activeStatement)) {
                    return (Statement) activeStatement;
                }
            }

            return null;
        }

        /**
         * @param succedent
         *            Succedent of a sequent.
         * @return True iff the given succedent has one formula with a break
         *         point statement, else null;
         */
        private boolean hasBreakPoint(final Semisequent succedent, final Services services, final Statement breakpoint) {
            return hasStmtForWhichPredicateHolds(succedent, services, new Predicate<Statement>() {
                @Override
                public boolean holdsFor(Statement arg) {
                    // Alternative for checking for the existence of any breakpoint:
                    // -> breakpoints.contains(arg)
                    return arg.equals(breakpoint);
                }
            });
        }

        /**
         * @param succedent
         *            Succedent of a sequent.
         * @param pred
         *            A decision predicate.
         * @return True iff the given succedent has one formula for which pred holds.
         */
        private boolean hasStmtForWhichPredicateHolds(final Semisequent succedent, final Services services, final Predicate<Statement> pred) {
            for (SequentFormula formula : succedent.asList()) {
                JavaBlock javaBlock = JoinRuleUtils.getJavaBlockRecursive(
                        formula.formula());

                StatementBlock blockWithoutMethodFrame = stripMethodFrame((StatementBlock) javaBlock.program(), services);

                if (blockWithoutMethodFrame.isEmpty()) {
                    continue;
                }

                SourceElement activeStatement = null;
                do {
                    final SourceElement oldActiveStatement = activeStatement;
                    activeStatement = JavaTools
                            .getActiveStatement(javaBlock);

                    if (oldActiveStatement != null && oldActiveStatement.equals(activeStatement)) {
                        break;
                    }

                    try {
                        javaBlock = JavaTools.removeActiveStatement(javaBlock, services);
                    } catch (IndexOutOfBoundsException e) {
                        // No more statement to check
                        break;
                    }

                    if (activeStatement instanceof Statement
                            && pred.holdsFor((Statement) activeStatement)) {
                        return true;
                    }
                } while (true);
            }

            return false;
        }

    }

    private static interface Predicate<T> {
        boolean holdsFor(T arg);
    }

}
