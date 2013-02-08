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
