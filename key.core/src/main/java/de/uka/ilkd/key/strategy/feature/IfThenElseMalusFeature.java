/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.LRUCache;


/**
 * Feature that counts the IfThenElse operators above the focus of a rule application. When
 * operating in argument 2 or 3 (branches) of IfThenElse, a malus of 1 is added; when operating in
 * the argument 1 (condition), a bonus of -1 is added.
 */
public class IfThenElseMalusFeature implements Feature<Goal> {
    public static final Feature<Goal> INSTANCE = new IfThenElseMalusFeature();

    private IfThenElseMalusFeature() {}

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
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

            final var t = it.getSubTerm();
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
