package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;
import recoder.java.expression.operator.NewArray;

public class NewArrayWrapper extends NewArray {

    /**
     *
     */
    private static final long serialVersionUID = -3838799869300845065L;
    private final Identifier scope;

    public NewArrayWrapper(NewArray proto, Identifier scope) {
        super(proto);
        this.scope = scope;
    }

    public NewArrayWrapper deepClone() {
        return new NewArrayWrapper(super.deepClone(), scope == null ? null : scope.deepClone());
    }

    public Identifier getScope() {
        return scope;
    }

}
