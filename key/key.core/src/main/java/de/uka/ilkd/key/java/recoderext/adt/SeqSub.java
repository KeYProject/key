package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.list.generic.ASTArrayList;


public class SeqSub extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = 9034359926577584988L;

    public SeqSub(Expression e1, Expression e2, Expression e3) {
        children = new ASTArrayList<Expression>(getArity());
        children.add(e1);
        children.add(e2);
        children.add(e3);
        makeParentRoleValid();
    }

    public SeqSub(ADTPrefixConstruct seq, RangeExpression range) {
        this(seq, (Expression) range.getChildAt(0), (Expression) range.getChildAt(1));
    }


    protected SeqSub(SeqSub proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SeqSub deepClone() {
        return new SeqSub(this);
    }


    @Override
    public int getArity() {
        return 3;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public String toSource() {
        return children.get(0).toSource() + "[" + children.get(1) + ".." + children.get(2) + "]";
    }


}
