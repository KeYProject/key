package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class Singleton extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = 5549648259903299451L;


    public Singleton(Expression lhs) {
        super(lhs);
        makeParentRoleValid();
    }


    protected Singleton(Singleton proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public Singleton deepClone() {
        return new Singleton(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }
}
