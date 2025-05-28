package de.uka.ilkd.key.java.recoderext.mst;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;
import recoder.java.Expression;

public class MSetDiff extends ADTPrefixConstruct {


    private static final long serialVersionUID = -6950638934821692317L;

    public MSetDiff(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected MSetDiff(MSetDiff proto) {
        super(proto);
        makeParentRoleValid();
    }



    @Override
    public Expression deepClone() {
        return new MSetDiff(this);
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
        return "\\mset_diff(" + children.get(0).toSource() + "," + children.get(1).toSource()
                + ")";
    }
}
