package de.uka.ilkd.key.java.recoderext;

import java.util.List;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.list.generic.ASTArrayList;

public class DLEmbeddedExpression extends Operator {

    private final String functionName;
    /**
     * @return the functionName
     */
    public String getFunctionName() {
        return functionName;
    }

    public DLEmbeddedExpression(String functionName, List<Expression> arguments) {
        this.functionName = functionName;
        children = new ASTArrayList<Expression>(arguments);
    }
    
    /**
     * Arity of an embedded JavaDL Expression depends upon the number of
     * arguments.
     */
    @Override
    public int getArity() {
        return children.size();
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public Expression deepClone() {
        return new DLEmbeddedExpression(functionName, children);
    }

    @Override
    public void accept(SourceVisitor v) {
        // TODO Implement DLEmbeddedExpression.accept
    }

}
