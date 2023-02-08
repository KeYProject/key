package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;


public class TwoState extends Modifier {

    private static final long serialVersionUID = 1408979308814683681L;

    public TwoState() {
    }

    protected TwoState(TwoState proto) {
        super(proto);
    }

    public TwoState deepClone() {
        return new TwoState(this);
    }

    public void accept(SourceVisitor v) {
    }

}
