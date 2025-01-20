/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * Binary feature that returns zero iff the replacewith- and find-parts of a Taclet are matched to
 * different terms.
 */
public class DiffFindAndReplacewithFeature extends BinaryTacletAppFeature {

    /** the single instance of this feature */
    public static final Feature INSTANCE = new DiffFindAndReplacewithFeature();

    private DiffFindAndReplacewithFeature() {}

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null && app.rule() instanceof RewriteTaclet
                : "Feature is only applicable to rewrite taclets";

        for (TacletGoalTemplate temp : ((Taclet) app.rule()).goalTemplates()) {
            RewriteTacletGoalTemplate rwtemp = (RewriteTacletGoalTemplate) temp;
            if (rwtemp.replaceWith().equalsModProperty(pos.subTerm(),
                IRRELEVANT_TERM_LABELS_PROPERTY)) {
                return false;
            }
        }
        return true;
    }
}
