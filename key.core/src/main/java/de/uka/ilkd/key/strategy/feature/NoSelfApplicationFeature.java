/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.ImmutableList;

/**
 * This feature checks that the position of application is not contained in the if-formulas. If the
 * rule application is admissible, zero is returned.
 */
public class NoSelfApplicationFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new NoSelfApplicationFeature();

    private NoSelfApplicationFeature() {}

    @Override
    protected boolean filter(TacletApp p_app, PosInOccurrence pos, Goal goal) {
        Debug.assertTrue(pos != null,
            "NoSelfApplicationFeature: Need to know the position of the application of the taclet");

        if (!p_app.ifInstsComplete()) {
            return true;
        }

        ImmutableList<IfFormulaInstantiation> ifInsts = p_app.ifFormulaInstantiations();

        Debug.assertTrue(ifInsts != null && !ifInsts.isEmpty(),
            "NoSelfApplicationFeature: Need to know the equation the taclet is used with");

        boolean noSelfApplication = true;
        for (IfFormulaInstantiation ifInst : ifInsts) {
            noSelfApplication =
                noSelfApplication && (ifInst.getConstrainedFormula() != pos.sequentFormula());
        }
        return noSelfApplication;
    }

}
