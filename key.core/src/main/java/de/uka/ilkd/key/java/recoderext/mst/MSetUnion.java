package de.uka.ilkd.key.java.recoderext.mst;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;
import de.uka.ilkd.key.java.recoderext.adt.SeqConcat;
import recoder.java.Expression;

public class MSetUnion extends ADTPrefixConstruct {

    private static final long serialVersionUID = -6850638934821692317L;

    public MSetUnion(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected MSetUnion(MSetUnion proto) {
        super(proto);
        makeParentRoleValid();
    }



    @Override
    public Expression deepClone() {
        return new MSetUnion(this);
    }

    @Override
    public int getArity() {
        return 2;
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public String toSource(){
        return "\\mset_union(" + children.get(0).toSource() + "," + children.get(1).toSource()
                + ")";
    }
}
