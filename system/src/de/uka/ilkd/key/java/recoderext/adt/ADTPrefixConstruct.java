package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

public abstract class ADTPrefixConstruct extends Operator implements ReferencePrefix {
    
    private ReferenceSuffix suffix;
    
    public ADTPrefixConstruct(){
        super();
    }
    
    public ADTPrefixConstruct(Expression unary){
        super(unary);
    }
    
    public ADTPrefixConstruct(Expression lhs, Expression rhs){
        super(lhs,rhs);
    }
    
    protected ADTPrefixConstruct(ADTPrefixConstruct proto){
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
        // SourceVisitors in RecodeR currently are only used to perform the toSource() operation.
        // One of them needs to be implemented in order for source code to be reproduced.
    }
    
    @Override
    public int getPrecedence(){
        return 0; // TODO remove from subclasses
    }
    
    @Override
    public String toString(){
        return toSource();
    }

}
