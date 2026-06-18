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

    /**
     * Maps rules to their justifications. All access is {@code synchronized} on this object: the
     * rule executor registers justifications (via {@code Goal.addTaclet} ->
     * {@code InitConfig.registerRuleIntroducedAtNode}) whenever a rule introduces a taclet, which
     * happens concurrently under the goal-level parallel prover; a
     * plain {@link LinkedHashMap} would corrupt under concurrent {@code addJustification}. The
     * {@code addJustification} compound (contains-then-iterate-then-put) must also stay atomic.
     */
    private final Map<RuleKey, RuleJustification> rule2Justification = new LinkedHashMap<>();

    public synchronized void addJustification(Rule r, RuleJustification j) {
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

    public synchronized @Nullable RuleJustification getJustification(Rule r) {
        return rule2Justification.get(new RuleKey(r));
    }

    public synchronized @Nullable RuleJustification getJustification(RuleApp r,
            LogicServices services) {
        RuleJustification just = getJustification(r.rule());
        if (just instanceof ComplexRuleJustification) {
            return ((ComplexRuleJustification) just).getSpecificJustification(r, services);
        } else {
            return just;
        }
    }

    public synchronized void removeJustificationFor(Rule rule) {
        rule2Justification.remove(new RuleKey(rule));
    }

    public synchronized RuleJustificationInfo copy() {
        RuleJustificationInfo info = new RuleJustificationInfo();
        info.rule2Justification.putAll(rule2Justification);
        return info;
    }
}
