package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

public class Intersect extends BinaryOperator {

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
