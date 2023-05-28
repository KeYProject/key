package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import java.util.List;

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
        return PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnIntersect(this);
    }

}
