package de.uka.ilkd.key.java.expression.operator.mst;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

public class MSetUnion extends BinaryOperator {
    public MSetUnion(ExtList children) {
        super(children);
    }

    public MSetUnion(Expression msetA, Expression msetB) {
        super(msetA, msetB);
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnMSetUnion(this);
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
