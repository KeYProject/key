/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.RuleApp;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;


public class ComplexRuleJustificationBySpec implements ComplexRuleJustification {

    private static final Logger LOGGER =
            LoggerFactory.getLogger(ComplexRuleJustificationBySpec.class);

    private final Map<RuleApp, RuleJustificationBySpec> app2Just =
        new LinkedHashMap<>();


    public boolean isAxiomJustification() {
        return false;
    }


    public @Nonnull RuleJustification getSpecificJustification(RuleApp app, TermServices services) {
        RuleJustification result = app2Just.get(app);
        if (result == null) {
            LOGGER.error("Rule app without stored justification: " + app +
                    " (" + app.rule().name() + ")");
            // even if we miss the map, continue with "this" as justification
            return this;
        }
        return result;
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
