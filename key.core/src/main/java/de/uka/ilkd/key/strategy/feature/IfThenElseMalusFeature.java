/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

import org.key_project.util.LRUCache;


/**
 * Feature that counts the IfThenElse operators above the focus of a rule application. When
 * operating in argument 2 or 3 (branches) of IfThenElse, a malus of 1 is added; when operating in
 * the argument 1 (condition), a bonus of -1 is added.
 */
public class IfThenElseMalusFeature implements Feature {
    public static final Feature INSTANCE = new IfThenElseMalusFeature();

    private IfThenElseMalusFeature() {}

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        if (pos == null) {
            return NumberRuleAppCost.getZeroCost();
        }

        final ServiceCaches caches = goal.proof().getServices().getCaches();

        RuleAppCost resInt;
        final LRUCache<PosInOccurrence, RuleAppCost> ifThenElseMalusCache =
            caches.getIfThenElseMalusCache();
        synchronized (ifThenElseMalusCache) {
            resInt = ifThenElseMalusCache.get(pos);
        }

        if (resInt != null) {
            return resInt;
        }

        int res = 0;

        final PIOPathIterator it = pos.iterator();
        while (true) {
            final int ind = it.next();
            if (ind == -1) {
                break;
            }

            final Term t = it.getSubTerm();
            if (t.op() instanceof IfThenElse) {
                res = ind != 0 ? res + 1 : res - 1;
            }
        }

        resInt = NumberRuleAppCost.create(res);

        synchronized (ifThenElseMalusCache) {
            ifThenElseMalusCache.put(pos, resInt);
        }

        return resInt;
    }
}
