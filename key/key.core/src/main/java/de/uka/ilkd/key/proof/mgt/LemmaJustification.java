package de.uka.ilkd.key.proof.mgt;

/**
 * {@link RuleJustification} for taclets, that can be proven from other taclets.
 */
public class LemmaJustification implements RuleJustification {

    public static final LemmaJustification INSTANCE = new LemmaJustification();

    private LemmaJustification() {
    }

    @Override
    public boolean isAxiomJustification() {
        return false;
    }
}
