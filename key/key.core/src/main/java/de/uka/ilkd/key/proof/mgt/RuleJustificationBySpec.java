package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.Contract;


public class RuleJustificationBySpec implements RuleJustification {

    private final Contract spec;


    public RuleJustificationBySpec(Contract spec) {
        this.spec = spec;
    }


    /**
     * Contracts for stubs are considered axioms; other contracts not.
     */
    public boolean isAxiomJustification() {
        return spec.getTarget() instanceof IProgramMethod
                && !((IProgramMethod) spec.getTarget()).isModel()
                && ((IProgramMethod) spec.getTarget()).getBody() == null;
    }


    public Contract getSpec() {
        return spec;
    }
}
