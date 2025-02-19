/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * @author Alexander Weigl
 * @version 1 (20.03.23)
 */
class SimpleStringLabel implements BranchNamingFunction {
    private final String label;

    SimpleStringLabel(String label) {
        this.label = label;
    }

    @Override
    public String getName(Services services, SequentChangeInfo currentSequent,
            TacletApp tacletApp, MatchConditions matchConditions) {
        return label;
    }
}
