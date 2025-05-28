package de.uka.ilkd.key.java.expression.operator.mst;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

public class MSetIntersect extends BinaryOperator {


    public MSetIntersect(ExtList children) {
        super(children);
    }

    public MSetIntersect(Expression msetA, Expression msetB) {
        super(msetA, msetB);
    }



    @Override
    public void visit(Visitor v) {
    v.performActionOnMSetIntersect(this);
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }
}
