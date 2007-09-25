package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;


public class Assert extends JavaStatement implements ExpressionContainer {

    private Expression condition;
    private Expression message;

    public Assert(Expression condition, Expression message, PositionInfo pos) {
        super(pos);
        assert condition != null;
        this.condition = condition;
        this.message   = message; 
    }
   

    public Expression getExpressionAt(int index) {
        if (index == 0) { return condition; }
        index--;
        if (index == 0) { 
            if (message != null) { return message; }        
        }
        throw new IndexOutOfBoundsException();
    }

    public int getExpressionCount() {        
        return message == null ? 1 : 2;
    }

    public ProgramElement getChildAt(int index) {        
        return getExpressionAt(index);
    }

    public int getChildCount() {        
        return getExpressionCount();
    }

    public void visit(Visitor v) {
        v.performActionOnAssert(this);
    }

    public Expression getCondition() {
        return condition;
    }
    
    public Expression getMessage() {
        return message;
    }
    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printAssert(this);
    }
}
