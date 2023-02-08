package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class SetUnion extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = -8425018389934762589L;


    public SetUnion(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected SetUnion(SetUnion proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SetUnion deepClone() {
        return new SetUnion(this);
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }
}
