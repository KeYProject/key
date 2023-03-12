package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;
import recoder.java.expression.operator.New;

public class NewWrapper extends New {

    /**
     *
     */
    private static final long serialVersionUID = -2814303467813768233L;
    private final Identifier scope;

    public NewWrapper(New proto, Identifier scope) {
        super(proto);
        this.scope = scope;
    }

    public NewWrapper deepClone() {
        return new NewWrapper(super.deepClone(), scope == null ? null : scope.deepClone());
    }

    public Identifier getScope() {
        return scope;
    }

}
