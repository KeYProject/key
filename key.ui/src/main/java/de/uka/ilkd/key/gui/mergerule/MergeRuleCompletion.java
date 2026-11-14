/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.mergerule;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class completes the instantiation for a merge rule application. The user is queried for
 * partner goals and concrete merge rule to choose. If in forced mode, all potential partners and
 * the if-then-else merge method are chosen (no query is shown to the user).
 *
 * @author Dominic Scheurer
 */
@NullMarked
public class MergeRuleCompletion implements InteractiveRuleApplicationCompletion {

    /** Singleton instance */
    public static final MergeRuleCompletion INSTANCE = new MergeRuleCompletion();

    private static final MergeProcedure STD_CONCRETE_MERGE_RULE = MergeByIfThenElse.instance();

    private MergeRuleCompletion() {
    }

    @Override
    public @Nullable IBuiltInRuleApp complete(final IBuiltInRuleApp app, final Goal goal,
            boolean forced) {

        final MergeRuleBuiltInRuleApp mergeApp = (MergeRuleBuiltInRuleApp) app;
        final PosInOccurrence pio = mergeApp.posInOccurrence();
        if (pio == null) {
            // the merge rule is only applicable at a concrete position
            return null;
        }

        final ImmutableList<MergePartner> candidates =
            MergeRule.findPotentialMergePartners(goal, pio);

        ImmutableList<MergePartner> chosenCandidates = null;
        final MergeProcedure chosenRule;
        JTerm chosenDistForm = null; // null is admissible standard ==> auto
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

        final MergeRuleBuiltInRuleApp result =
            new MergeRuleBuiltInRuleApp((MergeRule) app.rule(), pio);
        result.setMergePartners(chosenCandidates);
        result.setConcreteRule(chosenRule);
        if (chosenDistForm != null) {
            // a null distinguishing formula selects the automatic generation, which is the
            // default of a freshly created rule application
            result.setDistinguishingFormula(chosenDistForm);
        }
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
