/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Generic interface for evaluating the cost of
 * a RuleApp with regard to a specific feature
 * (like term size, ...)
 */
public interface RuleAppFeature {

    /**
     * Evaluate the cost of a RuleApp.
     */
    public long cost(RuleApp app, Goal goal);

}
