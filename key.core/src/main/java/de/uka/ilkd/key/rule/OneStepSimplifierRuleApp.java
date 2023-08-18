/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.PosInOccurrence;

import org.key_project.util.collection.ImmutableList;

public class OneStepSimplifierRuleApp extends DefaultBuiltInRuleApp {

    /**
     * @see #shouldRestrictAssumeInsts()
     */
    private boolean restrictedIfInsts = false;
    private OneStepSimplifier.Protocol protocol;

    protected OneStepSimplifierRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    /**
     * @return the protocol, may be <code>null</code>
     */
    public OneStepSimplifier.Protocol getProtocol() {
        return protocol;
    }

    /**
     * @param protocol the protocol to set
     */
    public void setProtocol(OneStepSimplifier.Protocol protocol) {
        this.protocol = protocol;
    }

    /**
     * Whether the assumption instantiations of this rule application have been specified
     * correctly. May be false when loading old proofs or creating a new OSS step.
     */
    public boolean shouldRestrictAssumeInsts() {
        return restrictedIfInsts;
    }

    /**
     * Restrict the assume instantions usable in this rule application.
     *
     * @param assumeInsts available formulas for \assume instantiations
     */
    public void restrictAssumeInsts(ImmutableList<PosInOccurrence> assumeInsts) {
        this.restrictedIfInsts = true;
        setIfInsts(assumeInsts);
    }
}
