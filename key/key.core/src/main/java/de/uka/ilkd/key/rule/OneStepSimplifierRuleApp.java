/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.PosInOccurrence;

public class OneStepSimplifierRuleApp extends DefaultBuiltInRuleApp {

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

}
