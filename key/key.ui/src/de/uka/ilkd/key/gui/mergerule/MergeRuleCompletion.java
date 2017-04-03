package de.uka.ilkd.key.gui.mergerule;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.procedures.MergeIfThenElse;

/**
 * This class completes the instantiation for a join rule application. The user
 * is queried for partner goals and concrete join rule to choose. If in forced
 * mode, all potential partners and the if-then-else join method are chosen (no
 * query is shown to the user).
 * 
 * @author Dominic Scheurer
 */
public class MergeRuleCompletion implements InteractiveRuleApplicationCompletion {

    /** Singleton instance */
    public static final MergeRuleCompletion INSTANCE = new MergeRuleCompletion();

    private static final MergeProcedure STD_CONCRETE_JOIN_RULE = MergeIfThenElse
            .instance();

    private MergeRuleCompletion() {
    }

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp app, final Goal goal,
            boolean forced) {

        final MergeRuleBuiltInRuleApp joinApp = (MergeRuleBuiltInRuleApp) app;
        final PosInOccurrence pio = joinApp.posInOccurrence();

        final ImmutableList<MergePartner> candidates =
                MergeRule.findPotentialJoinPartners(goal, pio);

        ImmutableList<MergePartner> chosenCandidates =
                null;
        final MergeProcedure chosenRule;
        Term chosenDistForm = null; // null is admissible standard ==> auto
                                    // generation

        if (forced) {
            chosenCandidates = candidates;
            chosenRule = STD_CONCRETE_JOIN_RULE;
        }
        else {
            final MergePartnerSelectionDialog dialog =
                    new MergePartnerSelectionDialog(goal, pio, candidates, goal
                            .proof().getServices());
            dialog.setVisible(true);
            
            chosenCandidates = dialog.getChosenCandidates();
            chosenRule = dialog.getChosenJoinRule();
            chosenDistForm = dialog.getChosenDistinguishingFormula();
        }

        if (chosenCandidates == null || chosenCandidates.size() < 1) {
            return null;
        }

        final MergeRuleBuiltInRuleApp result =
                new MergeRuleBuiltInRuleApp(app.rule(), pio);
        result.setJoinPartners(chosenCandidates);
        result.setConcreteRule(chosenRule);
        result.setDistinguishingFormula(chosenDistForm);
        result.setJoinNode(goal.node());

        return result;
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    public static boolean checkCanComplete(IBuiltInRuleApp app) {
        return app instanceof MergeRuleBuiltInRuleApp;
    }

}
