package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import org.key_project.util.collection.ImmutableList;

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

        // goal must have the same sequent as its partner node
        if (!goal.sequent().equals(partnerNode.sequent())) {
            return null;
        }

        // Ensures that both nodes have the same partially instantiated NoPosTaclets (in particular
        // insert_hidden_ rules). Otherwise it would be a soundness problem.
        // TODO: this implementation works only if pruning in closed branches is enabled ...
        Goal partnerGoal = goal.proof().getClosedGoal(partnerNode);
        if (partnerGoal != null) {
            for (NoPosTacletApp npta : goal.indexOfTaclets().getPartialInstantiatedApps()) {
                if (!partnerGoal.indexOfTaclets().getPartialInstantiatedApps().contains(npta)) {
                    // different rules sets -> not applicable
                    return null;
                }
            }
        } else {
            // TODO: in this case, closing may be unsound!
            System.out.println("Warning: Closing by reference may be unsound, since partially " +
                "instantiated NoPosTacletApps could not be checked!");
        }

        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();
        //final Proof proof = resultGoal.proof();

        // TODO: mark as linked, add listeners in case the partner is pruned
        //resultGoal.setLinkedGoal(proof.getClosedGoal(partnerNode));
        //proof.closeGoal(resultGoal);

        return resultGoal.split(0);
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
