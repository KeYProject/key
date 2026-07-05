/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.rule.RuleKey;

import org.key_project.logic.LogicServices;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;

import org.jspecify.annotations.Nullable;


public class RuleJustificationInfo {

    private final Map<RuleKey, RuleJustification> rule2Justification = new LinkedHashMap<>();

    public void addJustification(Rule r, RuleJustification j) {
        final RuleKey ruleKey = new RuleKey(r);
        if (rule2Justification.containsKey(ruleKey)) {
            // TODO: avoid double registration of certain class axioms and remove then the below
            // check so that
            // always an exception will be thrown
            for (RuleKey key : rule2Justification.keySet()) {
                if (key.equals(ruleKey) && r != key.r) {
                    throw new IllegalArgumentException(
                        "A rule named " + r.name() + " has already been registered.");
                }
            }
        } else {
            rule2Justification.put(ruleKey, j);
        }
    }

    public @Nullable RuleJustification getJustification(Rule r) {
        return rule2Justification.get(new RuleKey(r));
    }

    public @Nullable RuleJustification getJustification(RuleApp r, LogicServices services) {
        RuleJustification just = getJustification(r.rule());
        if (just instanceof ComplexRuleJustification) {
            return ((ComplexRuleJustification) just).getSpecificJustification(r, services);
        } else {
            return just;
        }
    }

    public void removeJustificationFor(Rule rule) {
        rule2Justification.remove(new RuleKey(rule));
    }

    public RuleJustificationInfo copy() {
        RuleJustificationInfo info = new RuleJustificationInfo();
        for (Map.Entry<RuleKey, RuleJustification> entry : rule2Justification.entrySet()) {
            // proof-local justifications (dynamically introduced rules such as addrule taclets
            // or generated lemmas) refer to nodes of the proof they were created in; carrying
            // them into a copied configuration would leave stale entries there that collide
            // with the rule (re-)introductions of the new proof
            if (!entry.getValue().isProofLocal()) {
                info.rule2Justification.put(entry.getKey(), entry.getValue());
            }
        }
        return info;
    }
}
