package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.*;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.Set;

/**
 * This rule can be used to close a goal by reference to an already closed node. The referred node
 * must have exactly the same sequent as the goal where the rule shall be applied to. Furthermore,
 * both nodes must have the same partially instantiated NoPosTacletApps (e.g., insert_hidden_
 * rules) for the goal to be closable.
 *
 * @author Wolfram Pfeifer
 */
public final class CloseByReferenceRule implements BuiltInRule {
    /** the only instance of this rule */
    public static final CloseByReferenceRule INSTANCE = new CloseByReferenceRule();

    /** the display name as a string */
    private static final String DISPLAY_NAME = "CloseByReferenceRule";

    /** the name of this rule */
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    private CloseByReferenceRule() {
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // can only be applied on the sequent arrow, i.e., to the goal itself
        return pio == null;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new CloseByReferenceRuleApp(this, pos);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
        throws RuleAbortException {

        CloseByReferenceRuleApp app = (CloseByReferenceRuleApp) ruleApp;
        PosInOccurrence pio = app.posInOccurrence();

        assert pio == null;

        if (!app.complete()) {
            return null;
        }

        Node currentNode = goal.node();
        Node partnerNode = app.getPartner();

        // TODO: currently, the partner has to be closed (could probably be relaxed) ...
        if (!partnerNode.isClosed()) {
            return null;
        }

        // goal must have the same sequent as its partner node (strategy irrelevant term labels and
        // order of formulas are ignored)
        if (!goal.sequent().equalsModIrrelevantTermLabels(partnerNode.sequent())) {
            return null;
        }

        // Ensures that both nodes have the same partially instantiated NoPosTaclets (in particular
        // insert_hidden_ rules). Otherwise, it would be a soundness problem.
        if (!localRulesAreCompatible(goal, partnerNode)) {
            return null;
        }

        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();

        resultGoal.setBranchLabel("Closed by reference to node " + partnerNode.serialNr());

        Proof proof = goal.proof();
        proof.addProofTreeListener(new ProofTreeAdapter() {
            @Override
            public void proofPruned(ProofTreeEvent e) {
                // this additional check is necessary, because the partner node could have already
                // been removed by the pruning operation
                if (proof.find(partnerNode)) {
                    if (!partnerNode.isClosed()) {
                        // partnerNode was reopened by pruning -> reopen currentNode (deletes
                        // the CloseByReferenceRule application)
                        proof.pruneProof(currentNode);

                        // the listener is not needed anymore
                        proof.removeProofTreeListener(this);
                    }
                }
            }
        });

        return resultGoal.split(0);
    }

    /**
     * Checks if the local rules (e.g., insert_hidden rules) of the goal are compatible to those
     * available at the node. Compatible means that each rule available at partnerNode must also
     * be available at currentGoal, however, currentGoal may have additional local rules.
     * @param currentGoal the goal which shall be closed by reference
     * @param partnerNode the potential reference partner which could be used to close the goal
     * @return true iff the rules are compatible
     */
    public static boolean localRulesAreCompatible(Goal currentGoal, Node partnerNode) {
        // collect all locally introduced rules that could differ between current and partner node
        Node currentNode = currentGoal.node();
        Node commonAncestor = currentNode.commonAncestor(partnerNode);
        Set<NoPosTacletApp> localTaclets = new HashSet<>();
        Node n = partnerNode;
        while (n != commonAncestor) {
            for (NoPosTacletApp localApp : n.getLocalIntroducedRules()) {
                localTaclets.add(localApp);
            }
            n = n.parent();
        }

        // closing by reference is only allowed if the referenced node does not have hidden rules
        // which are not present in the goal to close. Otherwise it would be a soundness problem.
        for (NoPosTacletApp localApp : localTaclets) {
            // this is probably slow, but should be ok since localTaclets is of small size ...
            if (!currentGoal.indexOfTaclets().getPartialInstantiatedApps().contains(localApp)) {
                // found at least one different -> not applicable
                return false;
            }
        }
        return true;
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
    public String toString() {
        return displayName();
    }

    /**
     * Rule application class for closing by reference. Is complete iff the partner node which
     * the goal should refer to has been set (by using the setter method).
     *
     * @author Wolfram Pfeifer
     */
    public static final class CloseByReferenceRuleApp extends AbstractBuiltInRuleApp {
        /** The partner the goal refers to. Must be closed already. */
        private Node partner;

        private CloseByReferenceRuleApp(BuiltInRule rule, PosInOccurrence pio) {
            super(rule, pio);
        }

        @Override
        public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
            return this;
        }

        @Override
        public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
            return this;
        }

        @Override
        public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
            return this;
        }

        @Override
        public boolean complete() {
            return partner != null;
        }

        @Override
        public String toString() {
            return "BuiltInRule: " + rule().name();
        }

        public Node getPartner() {
            return partner;
        }

        public void setPartner(Node partner) {
            this.partner = partner;
        }
    }
}
