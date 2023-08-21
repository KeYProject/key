/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.clearSemisequent;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getLocationVariables;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getUpdateLeftSideLocations;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.substConstantsByFreshVars;

/**
 * Rule for closing a partner goal after a merge operation. It does so by adding a formula
 * corresponding to the new merge node as an implicative premise to the goal to close; if the merge
 * rule is sound, the such manipulated goal should be closable by KeY. This particular way for
 * closing partner goals should ensure that proofs can only be closed for sound merge rules, i.e.
 * rules producing merge states that are weakenings of the parent states.
 * <p>
 *
 * TODO: If a user attempts to prune away a "closed" partner node, he/she should also be asked
 * whether the corresponding merge node should also be pruned. Otherwise, the user might
 * accidentally make it harder to close the whole proof (Add this to the bug tracker after merging
 * the merge branch into master).
 *
 * @author Dominic Scheurer
 */
public class CloseAfterMerge implements BuiltInRule {

    public static final String MERGE_GENERATE_IS_WEAKENING_GOAL_CFG =
        "mergeGenerateIsWeakeningGoal";
    public static final String MERGE_GENERATE_IS_WEAKENING_GOAL_CFG_ON =
        MERGE_GENERATE_IS_WEAKENING_GOAL_CFG + ":on";
    private static final String MERGED_NODE_IS_WEAKENING_TITLE = "Merged node is weakening";

    private static final String DISPLAY_NAME = "CloseAfterMerge";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public static final CloseAfterMerge INSTANCE = new CloseAfterMerge();

    /**
     * Hint to refactor the final weakening term.
     */
    public static final String FINAL_WEAKENING_TERM_HINT = "finalWeakeningTerm";

    private CloseAfterMerge() {
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

    @Nonnull
    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services,
            final RuleApp ruleApp) throws RuleAbortException {
        final TermLabelState termLabelState = new TermLabelState();

        assert ruleApp instanceof CloseAfterMergeRuleBuiltInRuleApp : //
                "Rule app for CloseAfterMerge has to be an instance of CloseAfterMergeRuleBuiltInRuleApp";

        CloseAfterMergeRuleBuiltInRuleApp closeApp = (CloseAfterMergeRuleBuiltInRuleApp) ruleApp;

        final boolean generateIsWeakeningGoal = goal.proof().getSettings().getChoiceSettings()
                .getDefaultChoices().containsKey(MERGE_GENERATE_IS_WEAKENING_GOAL_CFG)
                && goal.proof().getSettings().getChoiceSettings().getDefaultChoices()
                        .get(MERGE_GENERATE_IS_WEAKENING_GOAL_CFG)
                        .equals(MERGE_GENERATE_IS_WEAKENING_GOAL_CFG_ON);

        ImmutableList<Goal> jpNewGoals = goal.split(generateIsWeakeningGoal ? 2 : 1);

        final Goal linkedGoal = jpNewGoals.head();
        linkedGoal.setBranchLabel(
            "Merged with node " + closeApp.getCorrespondingMergeNode().parent().serialNr());
        linkedGoal.setLinkedGoal(goal);

        // Add a listener to close this node if the associated merge
        // node has also been closed, and to remove the mark as linked
        // node if the merge node has been pruned.
        final Node mergeNodeF = closeApp.getCorrespondingMergeNode();
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

                if (e.getGoals().size() == 0 && mergeNodeF.isClosed()) {
                    // The merged node was closed; now also close this node.

                    e.getSource().closeGoal(linkedGoal);
                    linkedGoal.clearAndDetachRuleAppIndex();
                }

            }

        });

        if (generateIsWeakeningGoal) {
            final Goal ruleIsWeakeningGoal = jpNewGoals.tail().head();
            ruleIsWeakeningGoal.setBranchLabel(MERGED_NODE_IS_WEAKENING_TITLE);

            Term isWeakeningForm = getSyntacticWeakeningFormula(closeApp, ruleIsWeakeningGoal);
            isWeakeningForm = TermLabelManager.refactorTerm(termLabelState, services, null,
                isWeakeningForm, this, ruleIsWeakeningGoal, FINAL_WEAKENING_TERM_HINT, null);
            // Delete previous sequents
            clearSemisequent(ruleIsWeakeningGoal, true);
            clearSemisequent(ruleIsWeakeningGoal, false);
            ruleIsWeakeningGoal.addFormula(new SequentFormula(isWeakeningForm), false, true);
            TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(), this,
                ruleIsWeakeningGoal, null, null);
        }

        return jpNewGoals;
    }

    /**
     * Constructs the actual syntactic weakening formula \phi(s1, s2) expressing that s2 is a
     * weakening of s1.
     *
     * @param closeApp The rule application containing the required data.
     * @param isWeakeningGoal The {@link Proof} {@link Goal} for the logical weakening formula.
     *
     * @return The syntactic weakening formula for the instantiated
     *         {@link CloseAfterMergeRuleBuiltInRuleApp}.
     */
    private Term getSyntacticWeakeningFormula(CloseAfterMergeRuleBuiltInRuleApp closeApp,
            Goal isWeakeningGoal) {
        final Services services = isWeakeningGoal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();

        ImmutableSet<LocationVariable> allLocs = DefaultImmutableSet.nil();
        allLocs = allLocs
                .union(getUpdateLeftSideLocations(closeApp.getPartnerSEState().getSymbolicState()));
        allLocs =
            allLocs.union(getUpdateLeftSideLocations(closeApp.getMergeState().getSymbolicState()));
        allLocs = allLocs.union(
            getLocationVariables(closeApp.getPartnerSEState().getPathCondition(), services));
        allLocs = allLocs
                .union(getLocationVariables(closeApp.getMergeState().getPathCondition(), services));

        final LinkedList<Term> origQfdVarTerms = new LinkedList<>();

        // Collect sorts and create logical variables for
        // closing over program variables.
        final LinkedList<Sort> argSorts = new LinkedList<>();
        for (LocationVariable var : allLocs) {
            argSorts.add(var.sort());
            origQfdVarTerms.add(tb.var(var));
        }

        // Create and register the new predicate symbol
        final Name predicateSymbName = new Name(tb.newName("P"));

        final Function predicateSymb =
            new Function(predicateSymbName, Sort.FORMULA, new ImmutableArray<>(argSorts));

        final Goal mergedGoal =
            services.getProof().getOpenGoal(closeApp.getMergeState().getCorrespondingNode());

        isWeakeningGoal.getLocalNamespaces().functions().add(predicateSymb);
        isWeakeningGoal.getLocalNamespaces().add(mergedGoal.getLocalNamespaces());
        isWeakeningGoal.getLocalNamespaces().add(mergedGoal.getLocalNamespaces().getParent());

        // Create the predicate term
        final Term predTerm = tb.func(predicateSymb, origQfdVarTerms.toArray(new Term[] {}));

        // Obtain set of new Skolem constants in merge state
        HashSet<Function> newConstants = closeApp.getNewNames().stream()
                .map(name -> isWeakeningGoal.getLocalNamespaces().functions().lookup(name))
                .collect(Collectors.toCollection(LinkedHashSet::new));

        //@formatter:off
        // Create the formula \forall v1,...,vn. (C2 -> {U2}P(...)) -> (C1 -> {U1}P(...))
        //@formatter:on
        Term result = tb.imp(
            allClosure(
                tb.imp(closeApp.getMergeState().getPathCondition(),
                    tb.apply(closeApp.getMergeState().getSymbolicState(), predTerm)),
                newConstants, services),
            tb.imp(closeApp.getPartnerSEState().getPathCondition(),
                tb.apply(closeApp.getPartnerSEState().getSymbolicState(), predTerm)));

        return result;
    }

    /**
     * Universally closes all logical variables in the given term. Before, all Skolem constants in
     * the term are replaced by fresh logical variables, where multiple occurrences of the same
     * constant are replaced by the same variable.
     *
     * @param term Term to universally close.
     * @param constsToReplace Skolem constants to replace before the universal closure.
     * @param services The services object.
     * @return A new term which is equivalent to the universal closure of the argument term, with
     *         Skolem constants in constsToReplace having been replaced by fresh variables before.
     */
    private Term allClosure(final Term term, final HashSet<Function> constsToReplace,
            Services services) {
        TermBuilder tb = services.getTermBuilder();

        Term termWithReplConstants = substConstantsByFreshVars(term, constsToReplace,
            new HashMap<>(), services);

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
        return new CloseAfterMergeRuleBuiltInRuleApp(this, pos);
    }

    /**
     * Creates a complete CloseAfterMergeBuiltInRuleApp.
     *
     * @param pio Position of the Update-ProgramCounter formula.
     * @param thePartnerNode The partner node to close.
     * @param correspondingMergeNode The corresponding merge node that is not closed. This is needed
     *        to add a reference to its parent in the partner goal at the place of this rule
     *        application.
     * @param mergeNodeState The SE state for the merge node; needed for adding an implicative
     *        premise ensuring the soundness of merge rules.
     * @param partnerState The SE state for the partner node.
     * @param pc The program counter common to the two states -- a formula of the form U\<{...}\>
     *        PHI, where U is an update in normal form and PHI is a DL formula).
     * @param newNames The set of new names (of Skolem constants) introduced in the merge.
     * @return A complete {@link CloseAfterMergeRuleBuiltInRuleApp}.
     */
    public CloseAfterMergeRuleBuiltInRuleApp createApp(PosInOccurrence pio, Node thePartnerNode,
            Node correspondingMergeNode, SymbolicExecutionState mergeNodeState,
            SymbolicExecutionState partnerState, Term pc, Set<Name> newNames) {
        return new CloseAfterMergeRuleBuiltInRuleApp(this, pio, thePartnerNode,
            correspondingMergeNode, mergeNodeState, partnerState, pc, newNames);
    }

}
