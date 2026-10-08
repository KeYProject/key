/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.mergerule;

import de.uka.ilkd.key.gui.fx.InteractiveRuleApplicationCompletionF;
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

/**
 * This class completes the instantiation for a merge rule application. The user is queried for
 * partner goals and concrete merge rule to choose. If in forced mode, all potential partners and
 * the if-then-else merge method are chosen (no query is shown to the user).
 * <p>
 * Port of the Swing {@code de.uka.ilkd.key.gui.mergerule.MergeRuleCompletion} (key.ui, logic
 * unchanged, only the dialog call replaced by {@link MergePartnerSelectionDialogF}). It
 * implements the {@link InteractiveRuleApplicationCompletionF} seam and is ready for
 * registration at the future {@code WindowUserInterfaceControlF} — see the {@code joinmerge}
 * TODO comment in {@code MainWindowF} for the exact registration snippet.
 *
 * @author Dominic Scheurer (original Swing class)
 */
public class MergeRuleCompletionF implements InteractiveRuleApplicationCompletionF {

    /** Singleton instance (Swing: {@code MergeRuleCompletion.INSTANCE}). */
    public static final MergeRuleCompletionF INSTANCE = new MergeRuleCompletionF();

    private static final MergeProcedure STD_CONCRETE_MERGE_RULE = MergeByIfThenElse.instance();

    private MergeRuleCompletionF() {
    }

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp app, final Goal goal, boolean forced) {

        final MergeRuleBuiltInRuleApp mergeApp = (MergeRuleBuiltInRuleApp) app;
        final PosInOccurrence pio = mergeApp.posInOccurrence();

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
            final MergePartnerSelectionDialogF dialog = new MergePartnerSelectionDialogF(goal, pio,
                candidates, goal.proof().getServices(), null);
            dialog.show();

            chosenCandidates = dialog.getChosenCandidates();
            chosenRule = dialog.getChosenMergeRule();
            chosenDistForm = dialog.getChosenDistinguishingFormula();
        }

        if (chosenCandidates == null || chosenCandidates.isEmpty()) {
            return null;
        }

        final MergeRuleBuiltInRuleApp result =
            new MergeRuleBuiltInRuleApp((MergeRule) app.rule(), pio);
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

    /**
     * @param app the rule app
     * @return true iff this completion can handle merge rule apps (Swing
     *         {@code MergeRuleCompletion.checkCanComplete})
     */
    public static boolean checkCanComplete(IBuiltInRuleApp app) {
        return app instanceof MergeRuleBuiltInRuleApp;
    }

}
