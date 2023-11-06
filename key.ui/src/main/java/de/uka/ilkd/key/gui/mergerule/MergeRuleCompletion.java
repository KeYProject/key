/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.mergerule;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;

import org.key_project.util.collection.ImmutableList;

/**
 * This class completes the instantiation for a merge rule application. The user is queried for
 * partner goals and concrete merge rule to choose. If in forced mode, all potential partners and
 * the if-then-else merge method are chosen (no query is shown to the user).
 *
 * @author Dominic Scheurer
 */
public class MergeRuleCompletion implements InteractiveRuleApplicationCompletion {

    /** Singleton instance */
    public static final MergeRuleCompletion INSTANCE = new MergeRuleCompletion();

    private static final MergeProcedure STD_CONCRETE_MERGE_RULE = MergeByIfThenElse.instance();

    private MergeRuleCompletion() {
    }

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp app, final Goal goal, boolean forced) {

        final MergeRuleBuiltInRuleApp mergeApp = (MergeRuleBuiltInRuleApp) app;
        final PosInOccurrence pio = mergeApp.posInOccurrence();

        final ImmutableList<MergePartner> candidates =
            MergeRule.findPotentialMergePartners(goal, pio);

        ImmutableList<MergePartner> chosenCandidates = null;
        final MergeProcedure chosenRule;
        Term chosenDistForm = null; // null is admissible standard ==> auto
                                    // generation

        if (forced) {
            chosenCandidates = candidates;
            chosenRule = STD_CONCRETE_MERGE_RULE;
        } else {
            final MergePartnerSelectionDialog dialog =
                new MergePartnerSelectionDialog(goal, pio, candidates, goal.proof().getServices());
            dialog.setVisible(true);

            chosenCandidates = dialog.getChosenCandidates();
            chosenRule = dialog.getChosenMergeRule();
            chosenDistForm = dialog.getChosenDistinguishingFormula();
        }

        if (chosenCandidates == null || chosenCandidates.size() < 1) {
            return null;
        }

        final MergeRuleBuiltInRuleApp result = new MergeRuleBuiltInRuleApp(app.rule(), pio);
        result.setMergePartners(chosenCandidates);
        result.setConcreteRule(chosenRule);
        result.setDistinguishingFormula(chosenDistForm);
        result.setMergeNode(goal.node());

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
