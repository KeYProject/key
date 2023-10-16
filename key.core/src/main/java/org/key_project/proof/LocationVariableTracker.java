/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proof;

import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.OpCollectorJavaBlock;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.rule.RuleApp;

public class LocationVariableTracker implements RuleAppListener {
    /**
     * The "origin" of this variable. Used to indicate which
     * {@link de.uka.ilkd.key.rule.TacletApp} created a new program variable.
     */
    private final Map<LocationVariable, RuleApp> createdBy = new WeakHashMap<>();

    public static void handleProofLoad(Proof proof) {
        LocationVariableTracker self = new LocationVariableTracker();
        proof.register(self, LocationVariableTracker.class);
        proof.addRuleAppListener(self);
    }

    public RuleApp getCreatedBy(LocationVariable locationVariable) {
        return createdBy.get(locationVariable);
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        var rai = e.getRuleAppInfo();
        if (rai.getRuleApp().rule().displayName().equals("ifElseUnfold")) {
            rai.getReplacementNodes().forEach(x -> {
                var it = x.getNodeChanges();
                while (it.hasNext()) {
                    var change = it.next();
                    var sf = change.getPos().sequentFormula();
                    var collect = new OpCollectorJavaBlock();
                    sf.formula().execPreOrder(collect);
                    for (var op : collect.ops()) {
                        if (!(op instanceof LocationVariable) || createdBy.containsKey(op)) {
                            continue;
                        }
                        createdBy.put((LocationVariable) op, rai.getRuleApp());
                    }
                }
            });
        }
    }
}
