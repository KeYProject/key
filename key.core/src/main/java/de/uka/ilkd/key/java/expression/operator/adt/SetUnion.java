package de.uka.ilkd.key.java.expression.operator.adt;

import java.util.List;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

public class SetUnion extends BinaryOperator {
    public SetUnion(PositionInfo pi, List<Comment> c, Expression a, Expression b) {
        super(pi, c, a, b);
    }

    public SetUnion(ExtList changeList) {
        super(changeList);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnSetUnion(this);
    }

}
