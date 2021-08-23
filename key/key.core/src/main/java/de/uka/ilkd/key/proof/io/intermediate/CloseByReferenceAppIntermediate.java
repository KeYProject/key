package de.uka.ilkd.key.proof.io.intermediate;

public class CloseByReferenceAppIntermediate extends BuiltInAppIntermediate {

    private int partnerId = -1;

    public CloseByReferenceAppIntermediate(String ruleName, int partnerId) {
        super(ruleName, null, null, null, null);
        this.partnerId = partnerId;
    }

    public int getPartnerId() {
        return partnerId;
    }
}
