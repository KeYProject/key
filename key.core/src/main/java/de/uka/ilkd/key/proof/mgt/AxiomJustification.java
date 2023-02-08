package de.uka.ilkd.key.proof.mgt;


public class AxiomJustification implements RuleJustification {

    public static final AxiomJustification INSTANCE = new AxiomJustification();

    private AxiomJustification() {
    }

    public String toString() {
        return "axiom justification";
    }

    public boolean isAxiomJustification() {
        return true;
    }
}
