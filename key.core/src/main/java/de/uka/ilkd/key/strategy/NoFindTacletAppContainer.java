/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;

/**
 * Instances of this class are immutable
 */
public class NoFindTacletAppContainer extends TacletAppContainer {

    NoFindTacletAppContainer(NoPosTacletApp p_app, RuleAppCost p_cost, long p_age) {
        super(p_app, p_cost, p_age);
    }

    /**
     * @return true iff the stored rule app is applicable for the given sequent, i.e. always true
     *         since NoFindTaclets are not bound to a find-position (if-formulas are not considered)
     */
    @Override
    protected boolean isStillApplicable(Goal p_goal) {
        return true;
    }

}
