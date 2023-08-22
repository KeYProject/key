/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A list of branch naming function.
 *
 * @author Alexander Weigl
 * @version 1 (20.03.23)
 */
public class CompositionalBranchNamingFunction implements BranchNamingFunction {
    private final List<BranchNamingFunction> seq;

    public CompositionalBranchNamingFunction(List<BranchNamingFunction> seq) {
        this.seq = seq;
    }

    @Override
    public String getName(Services services, SequentChangeInfo currentSequent, TacletApp tacletApp,
            MatchConditions matchConditions) {
        var sb = new StringBuilder();
        for (BranchNamingFunction fn : seq) {
            sb.append(fn.getName(services, currentSequent, tacletApp, matchConditions));
        }
        return sb.toString();
    }
}
