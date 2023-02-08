package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public final class EmptyMapLiteral extends Literal {

    /**
     * generated UID
     */
    private static final long serialVersionUID = -4665241238978552904L;

    public static final EmptyMapLiteral INSTANCE = new EmptyMapLiteral();

    @Override
    public Expression deepClone() {
        return this;
    }

    @Override
    public void accept(SourceVisitor v) {
    }

    @Override
    public Object getEquivalentJavaType() {
        return null;
    }

    @Override
    public String toSource() {
        return "\\map_empty";
    }
}
