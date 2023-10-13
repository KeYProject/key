/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.informationflow.rule.InfFlowContractAppTaclet;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleKey;


public class RuleJustificationInfo {

    private final Map<RuleKey, RuleJustification> rule2justif =
        new LinkedHashMap<>();

    public void addJustification(Rule r, RuleJustification j) {
        final RuleKey ruleKey = new RuleKey(r);
        if (rule2justif.containsKey(ruleKey)) {
            // TODO: avoid double registration of certain class axioms and remove then the below
            // check so that
            // always an exception will be thrown
            for (RuleKey key : rule2justif.keySet()) {
                if (key.equals(ruleKey) && r != key.r) {
                    // FIXME weigl: hack
                    // throw new IllegalArgumentException("A rule named " + r.name()
                    // + "has already been registered.");

                }
            }
        } else {
            rule2justif.put(ruleKey, j);
        }
    }

    public RuleJustification getJustification(Rule r) {
        return rule2justif.get(new RuleKey(r));
    }

    public RuleJustification getJustification(RuleApp r, TermServices services) {
        RuleJustification just = getJustification(r.rule());
        if (just instanceof ComplexRuleJustification) {
            return ((ComplexRuleJustification) just).getSpecificJustification(r, services);
        } else {
            return just;
        }
    }

    public void removeJustificationFor(Rule rule) {
        if (InfFlowContractAppTaclet.hasType(rule)) {
            InfFlowContractAppTaclet.unregister(rule.name());
        }
        rule2justif.remove(new RuleKey(rule));
    }

    public RuleJustificationInfo copy() {
        RuleJustificationInfo info = new RuleJustificationInfo();
        info.rule2justif.putAll(rule2justif);
        return info;
    }
}
