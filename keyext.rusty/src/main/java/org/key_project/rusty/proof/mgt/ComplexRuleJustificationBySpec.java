/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.rusty.Services;
import org.key_project.rusty.rule.RuleApp;

public class ComplexRuleJustificationBySpec implements ComplexRuleJustification {
    private final Map<RuleApp, RuleJustificationBySpec> app2Just =
        new LinkedHashMap<>();

    public boolean isAxiomJustification() {
        return false;
    }

    public RuleJustification getSpecificJustification(RuleApp app, Services services) {
        RuleJustification result = app2Just.get(app);
        return result == null ? this : result;
    }


    public void add(RuleApp ruleApp, RuleJustificationBySpec just) {
        // assert !(just instanceof ComplexRuleJustification);
        app2Just.put(ruleApp, just);
    }

    @Override
    public String toString() {
        return "ComplexRuleJustificationBySpec[" + app2Just + "]";
    }
}
