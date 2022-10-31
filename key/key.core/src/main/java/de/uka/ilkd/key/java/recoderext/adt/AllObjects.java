package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class AllObjects extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = 3940415948467542340L;


    public AllObjects(Expression lhs) {
        super(lhs);
        makeParentRoleValid();
    }


    protected AllObjects(AllObjects proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public AllObjects deepClone() {
        return new AllObjects(this);
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
