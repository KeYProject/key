package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class SetMinus extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = -1824229344478712816L;


    public SetMinus(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected SetMinus(SetMinus proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SetMinus deepClone() {
        return new SetMinus(this);
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
