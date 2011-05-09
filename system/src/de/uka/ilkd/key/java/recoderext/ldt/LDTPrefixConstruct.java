package de.uka.ilkd.key.java.recoderext.ldt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

public abstract class LDTPrefixConstruct extends Operator implements ReferencePrefix {
    
    private ReferenceSuffix suffix;
    
    public LDTPrefixConstruct(){
        super();
    }
    
    public LDTPrefixConstruct(Expression unary){
        super(unary);
    }
    
    public LDTPrefixConstruct(Expression lhs, Expression rhs){
        super(lhs,rhs);
    }
    
    protected LDTPrefixConstruct(LDTPrefixConstruct proto){
        super(proto);
    }

    @Override
    public ReferenceSuffix getReferenceSuffix() {
        return suffix;
    }

    @Override
    public void setReferenceSuffix(ReferenceSuffix arg0) {
        suffix = arg0;
    }

    @Override
    public void accept(SourceVisitor arg0) {
        // TODO Auto-generated method stub
    }
    
    @Override
    public int getPrecedence(){
        return 0; // TODO remove from subclasses
    }

}
