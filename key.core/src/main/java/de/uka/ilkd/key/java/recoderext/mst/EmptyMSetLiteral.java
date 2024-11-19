package de.uka.ilkd.key.java.recoderext.mst;

import de.uka.ilkd.key.java.recoderext.adt.EmptySeqLiteral;
import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class EmptyMSetLiteral extends Literal {

    /**
     *
     */
    private static final long serialVersionUID = 8572271426600775146L;
    public static final EmptyMSetLiteral INSTANCE = new EmptyMSetLiteral();

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
        return "\\mset_empty";
    }
}

