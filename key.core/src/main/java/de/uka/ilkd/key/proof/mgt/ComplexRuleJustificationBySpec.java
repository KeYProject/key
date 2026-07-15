/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.key_project.logic.LogicServices;
import org.key_project.prover.rules.RuleApp;


public class ComplexRuleJustificationBySpec implements ComplexRuleJustification {

    /**
     * The per-application justifications, registered while the rule is applied. Under the
     * multi-core prover several worker threads apply contract rules at the same time and each
     * registration writes this one map (there is a single justification object per rule for the
     * whole proof), so the map must be safe for concurrent use. Keys are compared by identity,
     * values are immutable, and nothing iterates the map on the proving path -- a concurrent hash
     * map is exactly right. Proof saving later reads the entries through
     * {@link #getSpecificJustification(RuleApp, LogicServices)}; a lost registration would make
     * the saved proof unreloadable (the contract line would be missing).
     */
    private final Map<RuleApp, RuleJustificationBySpec> app2Just = new ConcurrentHashMap<>();

    @Override
    public boolean isAxiomJustification() {
        return false;
    }


    @Override
    public RuleJustification getSpecificJustification(RuleApp app, LogicServices services) {
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
