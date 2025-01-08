/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.feature.MutableState;

import org.key_project.logic.Name;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;

public class ContainsLabelNameFeature extends BinaryFeature {
    private final Name labelName;

    public ContainsLabelNameFeature(Name labelName) {
        this.labelName = labelName;
    }

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        if (pos == null)
            return false;
        var term = (de.uka.ilkd.key.logic.Term) pos.subTerm();
        return term.getLabel(labelName) != null;
    }
}
