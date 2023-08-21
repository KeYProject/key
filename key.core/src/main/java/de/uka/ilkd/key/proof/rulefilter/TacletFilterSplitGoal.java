/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Taclet;

public class TacletFilterSplitGoal extends TacletFilter {

    public final static TacletFilterSplitGoal INSTANCE = new TacletFilterSplitGoal();

    private TacletFilterSplitGoal() {
    }

    protected boolean filter(Taclet taclet) {
        return taclet.goalTemplates().size() > 1;
    }

}
