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

package de.uka.ilkd.key.rule.join;

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.clearSemisequent;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getLocationVariables;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getUpdateLeftSideLocations;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.substConstantsByFreshVars;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Rule for closing a partner goal after a join operation. It does so by adding
 * a formula corresponding to the new join node as an implicative premise to the
 * goal to close; if the join rule is sound, the such manipulated goal should be
 * closable by KeY. This particular way for closing partner goals should ensure
 * that proofs can only be closed for sound join rules, i.e. rules producing
 * join states that are weakenings of the parent states.
 * <p>
 * 
 * TODO: If a user attempts to prune away a "closed" partner node, he/she should
 * also be asked whether the corresponding join node should also be pruned.
 * Otherwise, the user might accidentally make it harder to close the whole
 * proof (Add this to the bug tracker after merging the join branch into
 * master).
 * 
 * @author Dominic Scheurer
 */
public class CloseAfterJoin implements BuiltInRule {

    private static final String JOIN_GENERATE_IS_WEAKENING_GOAL_CFG = "joinGenerateIsWeakeningGoal";
    private static final String JOIN_GENERATE_IS_WEAKENING_GOAL_CFG_ON =
            JOIN_GENERATE_IS_WEAKENING_GOAL_CFG + ":on";
    private static final String JOINED_NODE_IS_WEAKENING_TITLE = "Joined node is weakening";

    private static final String DISPLAY_NAME = "CloseAfterJoin";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public static final CloseAfterJoin INSTANCE = new CloseAfterJoin();

    private CloseAfterJoin() {
        /* Singleton class */
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services,
            final RuleApp ruleApp) throws RuleAbortException {

        assert ruleApp instanceof CloseAfterJoinRuleBuiltInRuleApp : "Rule app for CloseAfterJoin has to be an instance of CloseAfterJoinRuleBuiltInRuleApp";

        CloseAfterJoinRuleBuiltInRuleApp closeApp = (CloseAfterJoinRuleBuiltInRuleApp) ruleApp;

        final boolean generateIsWeakeningGoal = goal.proof().getSettings()
                .getChoiceSettings().getDefaultChoices()
                .containsKey(JOIN_GENERATE_IS_WEAKENING_GOAL_CFG)
                && goal.proof().getSettings().getChoiceSettings()
                        .getDefaultChoices()
                        .get(JOIN_GENERATE_IS_WEAKENING_GOAL_CFG)
                        .equals(JOIN_GENERATE_IS_WEAKENING_GOAL_CFG_ON);

        ImmutableList<Goal> jpNewGoals = goal.split(generateIsWeakeningGoal ? 2
                : 1);

        final Goal linkedGoal = jpNewGoals.head();
        linkedGoal.setBranchLabel("Joined with node "
                + closeApp.getCorrespondingJoinNode().parent().serialNr());
        linkedGoal.setLinkedGoal(goal);

        // Add a listener to close this node if the associated join
        // node has also been closed, and to remove the mark as linked
        // node if the join node has been pruned.
        final Node joinNodeF = closeApp.getCorrespondingJoinNode();
        services.getProof().addProofTreeListener(new ProofTreeAdapter() {

            @Override
            public void proofGoalsAdded(ProofTreeEvent e) {
                // Note: The method proofGoalsChanged(...) is only called when
                // a proof is pruned or when the GUI is updated. Therefore,
                // we have to exploit an already existing hack which calls
                // proofGoalsAdded with an empty list of arguments if a
                // goal is closed. Otherwise, we would not be notified about
                // a closed goal when loading a proof without the GUI (e.g.
                // in a JUnit test).

                if (e.getGoals().size() == 0 && joinNodeF.isClosed()) {
                    // The joined node was closed; now also close this node.

                    e.getSource().closeGoal(linkedGoal);
                    linkedGoal.clearAndDetachRuleAppIndex();
                }

            }

        });

        if (generateIsWeakeningGoal) {
            final Goal ruleIsWeakeningGoal = jpNewGoals.tail().head();
            ruleIsWeakeningGoal.setBranchLabel(JOINED_NODE_IS_WEAKENING_TITLE);

            final Term isWeakeningForm = getSyntacticWeakeningFormula(services,
                    closeApp);
            // Delete previous sequents
            clearSemisequent(ruleIsWeakeningGoal, true);
            clearSemisequent(ruleIsWeakeningGoal, false);
            ruleIsWeakeningGoal.addFormula(new SequentFormula(isWeakeningForm),
                    false, true);
        }

        return jpNewGoals;
    }

    /**
     * Constructs the actual syntactic weakening formula \phi(s1, s2) expressing
     * that s2 is a weakening of s1.
     * 
     * @param services
     *            The services object.
     * @param closeApp
     *            The rule application containing the required data.
     * @return The syntactic weakening formula for this.joinState and
     *         this.thisSEState.
     */
    private Term getSyntacticWeakeningFormula(Services services,
            CloseAfterJoinRuleBuiltInRuleApp closeApp) {
        TermBuilder tb = services.getTermBuilder();

        ImmutableSet<LocationVariable> allLocs = DefaultImmutableSet.nil();
        allLocs = allLocs.union(getUpdateLeftSideLocations(closeApp
                .getPartnerSEState().getSymbolicState()));
        allLocs = allLocs.union(getUpdateLeftSideLocations(closeApp
                .getJoinState().getSymbolicState()));
        allLocs = allLocs.union(getLocationVariables(closeApp
                .getPartnerSEState().getPathCondition(), services));
        allLocs = allLocs.union(getLocationVariables(closeApp.getJoinState()
                .getPathCondition(), services));

        final LinkedList<Term> origQfdVarTerms = new LinkedList<Term>();

        // Collect sorts and create logical variables for
        // closing over program variables.
        final LinkedList<Sort> argSorts = new LinkedList<Sort>();
        for (LocationVariable var : allLocs) {
            argSorts.add(var.sort());
            origQfdVarTerms.add(tb.var(var));
        }

        // Create and register the new predicate symbol
        final Name predicateSymbName = new Name(tb.newName("P"));

        final Function predicateSymb = new Function(predicateSymbName,
                Sort.FORMULA, new ImmutableArray<Sort>(argSorts));

        services.getNamespaces().functions().add(predicateSymb);

        // Create the predicate term
        final Term predTerm = tb.func(predicateSymb,
                origQfdVarTerms.toArray(new Term[] {}));

        // Obtain set of new Skolem constants in join state
        HashSet<Function> constantsOrigState = JoinRuleUtils
                .getSkolemConstants(closeApp.getPartnerSEState()
                        .getSymbolicState());
        HashSet<Function> newConstants = JoinRuleUtils
                .getSkolemConstants(closeApp.getJoinState().getSymbolicState());
        newConstants.removeAll(constantsOrigState);

        // Create the formula \forall v1,...,vn. (C2 -> {U2} P(...)) -> (C1 ->
        // {U1} P(...))
        Term result = tb.imp(
                allClosure(tb.imp(closeApp.getJoinState().getPathCondition(),
                        tb.apply(closeApp.getJoinState().getSymbolicState(),
                                predTerm)), newConstants, services), tb.imp(
                        closeApp.getPartnerSEState().getPathCondition(), tb
                                .apply(closeApp.getPartnerSEState()
                                        .getSymbolicState(), predTerm)));

        return result;
    }

    /**
     * Universally closes all logical variables in the given term. Before, all
     * Skolem constants in the term are replaced by fresh logical variables,
     * where multiple occurrences of the same constant are replaced by the same
     * variable.
     * 
     * @param term
     *            Term to universally close.
     * @param constsToReplace
     *            Skolem constants to replace before the universal closure.
     * @param services
     *            The services object.
     * @return A new term which is equivalent to the universal closure of the
     *         argument term, with Skolem constants in constsToReplace having
     *         been replaced by fresh variables before.
     */
    private Term allClosure(final Term term,
            final HashSet<Function> constsToReplace, Services services) {
        TermBuilder tb = services.getTermBuilder();

        Term termWithReplConstants = substConstantsByFreshVars(term,
                constsToReplace, new HashMap<Function, LogicVariable>(),
                services);

        return tb.all(termWithReplConstants.freeVars(), termWithReplConstants);
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return true;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new CloseAfterJoinRuleBuiltInRuleApp(this, pos);
    }

    /**
     * Creates a complete CloseAfterJoinBuiltInRuleApp.
     *
     * @param pio
     *            Position of the Update-ProgramCounter formula.
     * @param thePartnerNode
     *            The partner node to close.
     * @param correspondingJoinNode
     *            The corresponding join node that is not closed. This is needed
     *            to add a reference to its parent in the partner goal at the
     *            place of this rule application.
     * @param joinNodeState
     *            The SE state for the join node; needed for adding an
     *            implicative premise ensuring the soundness of join rules.
     * @param partnerState
     *            The SE state for the partner node.
     * @param pc
     *            The program counter common to the two states -- a formula of
     *            the form U\<{...}\> PHI, where U is an update in normal form
     *            and PHI is a DL formula).
     * @return A complete {@link CloseAfterJoinRuleBuiltInRuleApp}.
     */
    public CloseAfterJoinRuleBuiltInRuleApp createApp(PosInOccurrence pio,
            Node thePartnerNode, Node correspondingJoinNode,
            SymbolicExecutionState joinNodeState,
            SymbolicExecutionState partnerState, Term pc) {
        return new CloseAfterJoinRuleBuiltInRuleApp(this, pio, thePartnerNode,
                correspondingJoinNode, joinNodeState, partnerState, pc);
    }

}
