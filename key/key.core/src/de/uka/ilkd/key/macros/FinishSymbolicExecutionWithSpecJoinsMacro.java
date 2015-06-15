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
import de.uka.ilkd.key.java.statement.MethodFrame;
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
import de.uka.ilkd.key.macros.ProofMacro.ProgressBarListener;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.join.JoinRule;
import de.uka.ilkd.key.rule.join.JoinRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElseAntecedent;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedRuleApplicationManager;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO
 * 
 * @author Dominic Scheurer
 * @see FinishSymbolicExecutionMacro
 */
public class FinishSymbolicExecutionWithSpecJoinsMacro extends
    AbstractProofMacro {

    private HashSet<ProgramElement> breakpoints = new HashSet<ProgramElement>();
    private HashMap<ProgramElement, Node> commonParents = new HashMap<ProgramElement, Node>();
    private HashMap<ProgramElement, BlockContract> joinContracts = new HashMap<ProgramElement, BlockContract>();
    private HashSet<Goal> stoppedGoals = new HashSet<Goal>();
    private HashSet<JavaBlock> alreadySeen = new HashSet<JavaBlock>();

//    private UserInterfaceControl uic = null;

    public FinishSymbolicExecutionWithSpecJoinsMacro() {
    }

    public FinishSymbolicExecutionWithSpecJoinsMacro(
            HashSet<ProgramElement> breakpoints,
            HashMap<ProgramElement, Node> commonParents) {
        this.breakpoints = breakpoints;
        this.commonParents = commonParents;
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
        if (goals == null || goals.isEmpty()) {
            // should not happen, because in this case canApplyTo returns
            // false
            return null;
        }

        final IGoalChooser goalChooser = proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create();
        final ApplyStrategy applyStrategy = new ApplyStrategy(goalChooser);
        final ImmutableList<Goal> ignoredOpenGoals =
                setDifference(proof.openGoals(), goals);

        final ProofMacro macroAdapter = new SkipMacro() {
            @Override
            public String getName() { return ""; }
            @Override
            public String getDescription() { return "Anonymous macro"; }
        };
        macroAdapter.setNumberSteps(getNumberSteps());
        //
        // The observer to handle the progress bar
        final ProofMacroListener pml =  new ProgressBarListener(macroAdapter, goals.size(),
                                                                getNumberSteps(), listener);
        applyStrategy.addProverTaskObserver(pml);
        // add a focus manager if there is a focus
        if(posInOcc != null && goals != null) {
            AutomatedRuleApplicationManager realManager = null;
            FocussedRuleApplicationManager manager = null;
            for (Goal goal: goals) {
                realManager = goal.getRuleAppManager();
                realManager.clearCache();
                manager = new FocussedRuleApplicationManager(realManager, goal, posInOcc);
                goal.setRuleAppManager(manager);
            }
        }

        // set a new strategy.
        Strategy oldStrategy = proof.getActiveStrategy();
        FilterSymbexStrategy strategy = createStrategy(proof, posInOcc);
        proof.setActiveStrategy(strategy);

        ProofMacroFinishedInfo info =
                new ProofMacroFinishedInfo(this, goals, proof);
        try {
            // find the relevant goals
            // and start
            boolean joined;
            do {
                joined = false;
                applyStrategy.start(proof, goals);
                synchronized(applyStrategy) { // wait for applyStrategy to finish its last rule application
                    if(applyStrategy.hasBeenInterrupted()) { // reraise interrupted exception if necessary
                        throw new InterruptedException();
                    }
                }
                
                Pair<Goal, JoinRuleBuiltInRuleApp> joinInfo = strategy.getAndResetJoinInformation();
                if (joinInfo != null) {
                    joinInfo.first.apply(joinInfo.second);
                    joined = true;
                }
            } while (joined);
        } finally {
            // this resets the proof strategy and the managers after the automation
            // has run
            for (final Goal openGoal : proof.openGoals()) {
                AutomatedRuleApplicationManager manager = openGoal.getRuleAppManager();
                // touch the manager only if necessary
                if(manager.getDelegate() != null) {
                    while(manager.getDelegate() != null) {
                        manager = manager.getDelegate();
                    }
                    manager.clearCache();
                    openGoal.setRuleAppManager(manager);
                }
            }
            final ImmutableList<Goal> resultingGoals =
                    setDifference(proof.openGoals(), ignoredOpenGoals);
            info = new ProofMacroFinishedInfo(this, resultingGoals);
            proof.setActiveStrategy(oldStrategy);
//            doPostProcessing(proof);
            applyStrategy.removeProverTaskObserver(pml);
        }
        return info;
    }
    

    /**
     * 
     * TODO: Document.
     *
     * @param goals1
     * @param goals2
     * @return
     */
    private static ImmutableList<Goal> setDifference(ImmutableList<Goal> goals1,
                                                     ImmutableList<Goal> goals2) {
        ImmutableList<Goal> difference = goals1;
        for (Goal goal : goals2) {
            difference = difference.removeFirst(goal);
        }
        return difference;
    }

    protected FilterSymbexStrategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        // Need to clear the data structures since no new instance of this
        // macro is created across multiple calls, so sometimes it would have
        // no effect in a successive call.
        breakpoints.clear();
        alreadySeen.clear();
        commonParents.clear();
        stoppedGoals.clear();

        return new FilterSymbexStrategy(proof.getActiveStrategy());
    }

    /**
     * @param succedent
     *            Succedent of a sequent.
     * @return A Statement (the registered breakpoint) iff the given succedent has one formula with a break point
     *         statement, else null;
     */
    private Statement getBreakPoint(Semisequent succedent) {
        for (SequentFormula formula : succedent.asList()) {
            Statement activeStmt = (Statement) JavaTools
                    .getActiveStatement(getJavaBlockRecursive(formula
                            .formula()));
            if (breakpoints.contains(activeStmt)) {
                return activeStmt;
            }
        }

        return null;
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
        
        private boolean enforceJoin = false;
        
        private Pair<Goal, JoinRuleBuiltInRuleApp> joinInformation = null;
        
        /**
         * TODO: Document.
         *
         * @return
         */
        public Pair<Goal, JoinRuleBuiltInRuleApp> getAndResetJoinInformation() {
            final Pair<Goal, JoinRuleBuiltInRuleApp> oldJoinInformation = joinInformation;
            enforceJoin = false;
            joinInformation = null;
            return oldJoinInformation;
        }

        public FilterSymbexStrategy(Strategy delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if (enforceJoin) {
                return false;
            }
            
            if (!hasModality(goal.node())) {
                return false;
            }
            
            Statement breakpoint;
            if ((breakpoint = getBreakPoint(goal.sequent().succedent())) != null) {
                final ImmutableList<Goal> subtreeGoals = goal.proof().getSubtreeGoals(commonParents.get(breakpoint));
                boolean allStopped = true;
                for (Goal subGoal : subtreeGoals) {
                    if (!subGoal.equals(goal)) {
                        allStopped = allStopped && stoppedGoals.contains(subGoal);
                    }
                }
                
                if (allStopped) {
                    // Not it's time for a join
                    final JoinRule joinRule = JoinRule.INSTANCE;

                    final Node joinNode = goal.node();
                    final PosInOccurrence joinPio = getPioForBreakpoint(breakpoint, goal.sequent());
                    final JoinRuleBuiltInRuleApp joinApp = (JoinRuleBuiltInRuleApp) joinRule
                            .createApp(joinPio, goal.proof().getServices());

                    {
                        joinApp.setJoinPartners(JoinRule.findPotentialJoinPartners(goal, joinPio));
                        joinApp.setConcreteRule(joinContracts.get(breakpoint).getJoinProcedure());
                        joinApp.setJoinNode(joinNode);
                    }
                    
                    for (Goal subgoal : subtreeGoals) {
                        stoppedGoals.remove(subgoal);
                    }
                    breakpoints.remove(breakpoint);
                    commonParents.remove(breakpoint);
                    
//                    goal.apply(joinApp);
                    joinInformation = new Pair<Goal, JoinRuleBuiltInRuleApp>(goal, joinApp);
                    enforceJoin = true;
                } else {
                    stoppedGoals.add(goal);
                }
                
                return false;
            }

            if (pio != null) {
                JavaBlock theJavaBlock = getJavaBlockRecursive(pio.subTerm());
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
                }

                // Find break points
                breakpoints.addAll(findJoinPoints((StatementBlock) theJavaBlock
                        .program(), goal));

                if (app.rule().name().toString()
                        .equals("One Step Simplification")) {

                    // We allow One Step Simplification, otherwise we sometimes
                    // would
                    // have to do a simplification ourselves before joining
                    // nodes.
                    return true;

                }
                else if (breakpoints.contains((ProgramElement) activeStmt)) {
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
         * @param breakpoint
         * @param sequent
         * @return
         */
        private PosInOccurrence getPioForBreakpoint(Statement breakpoint, Sequent sequent) {
            Semisequent succedent = sequent.succedent();
            
            for (SequentFormula formula : succedent) {
                Statement activeStmt = (Statement) JavaTools
                        .getActiveStatement(getJavaBlockRecursive(formula
                                .formula()));
                
                if (activeStmt.equals(breakpoint)) {
                    return new PosInOccurrence(formula, PosInTerm.getTopLevel(), false);
                }
            }
            
            return null;
        }

        /**
         * Removes the <code>try { method-frame { ... }}</code> parts from the
         * given statement block, i.e. returns the inner code. If there is
         * nothing to remove, the original block is returned.
         *
         * @param sb
         *            The statement block to remove the try/method-frame parts
         *            from.
         * @return The stripped inner statement block or the original argument,
         *         if the removal was not applicable.
         */
        private StatementBlock stripMethodFrame(final StatementBlock sb) {
            try {
                if (sb.getBody().get(0) instanceof Try) {
                    Try theTry = (Try) sb.getBody().get(0);
                    if (theTry.getBody().getBody().get(0) instanceof MethodFrame) {
                        MethodFrame theMethodFrame = (MethodFrame) theTry.getBody()
                                .getBody().get(0);
                        return theMethodFrame.getBody();
                    }
                }
            }
            catch (ArrayIndexOutOfBoundsException e) {}

            return sb;
        }

        /**
         * Returns a set of join points for the given statement block. Join points
         * are directly registered once they are found.
         * 
         * @param toSearch
         *            The statement block to search for join points.
         * @param goal The goal corresponding to the statement block.
         * @return A set of join points for the given statement block.
         */
        private HashSet<ProgramElement> findJoinPoints(final StatementBlock toSearch,
                final Goal goal) {
            final Services services = goal.proof().getServices();
            final HashSet<ProgramElement> result = new HashSet<ProgramElement>();

            if (toSearch.isEmpty()) {
                return result;
            }

            StatementBlock blockWithoutMethodFrame = stripMethodFrame(toSearch);
            
            if (blockWithoutMethodFrame.isEmpty()) {
                return result;
            }
            
            Statement firstElem = blockWithoutMethodFrame.getBody().get(0);
            ImmutableSet<BlockContract> contracts;
            if (firstElem instanceof StatementBlock
                    && !(contracts = services.getSpecificationRepository()
                            .getBlockContracts((StatementBlock) firstElem))
                            .isEmpty()
                    && contracts.iterator().next().hasJoinProcedure()) {
                if (blockWithoutMethodFrame.getBody().size() > 1) {
                    Statement breakpoint = blockWithoutMethodFrame.getBody().get(1);
                    breakpoints.add(breakpoint);
                    commonParents.put(breakpoint, goal.node());
                    joinContracts.put(breakpoint, contracts.iterator().next());
                }
            }

            return result;
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.macros.ProofMacro#canApplyTo(de.uka.ilkd.key.proof.Proof, org.key_project.util.collection.ImmutableList, de.uka.ilkd.key.logic.PosInOccurrence)
     */
    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            PosInOccurrence posInOcc) {
        return goals != null && !goals.isEmpty();
    }

}
