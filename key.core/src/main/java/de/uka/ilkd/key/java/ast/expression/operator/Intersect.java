package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Expression;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

public class Intersect extends BinaryOperator {
    public Intersect(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, lhs, rhs);
    }

    public Intersect(ExtList children) {
        super(children);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return Operator.PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnIntersect(this);
    }

}
