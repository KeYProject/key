/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.NewRuleListener;
import de.uka.ilkd.key.rule.RuleApp;


/**
 *
 */
public interface AutomatedRuleApplicationManager extends NewRuleListener {

    /**
     * Clear existing caches of applicable rules
     */
    void clearCache();

    /**
     * @return the first applicable rule app, i.e. the least expensive element of the heap that is
     *         not obsolete and caches the result of this operation to save some time the next time
     *         the method nextAndCache() or next() is called. A call of next() empties the cache
     *         again.
     */
    RuleApp peekNext();

    /**
     * @return the next rule that is supposed to be applied
     */
    RuleApp next();

    /**
     * Set the goal <code>this</code> is the rule app manager for
     */
    void setGoal(Goal p_goal);

    AutomatedRuleApplicationManager copy();

}
