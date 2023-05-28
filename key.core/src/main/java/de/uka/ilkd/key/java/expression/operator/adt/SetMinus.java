package de.uka.ilkd.key.java.expression.operator.adt;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

import static org.antlr.tool.LeftRecursiveRuleAnalyzer.ASSOC.right;

public class SetMinus extends BinaryOperator {

    public SetMinus(PositionInfo pi, List<Comment> c, Expression child, Expression right) {
        super(pi, c, child, right);
    }

    public SetMinus(ExtList changeList) {
        super(changeList);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnSetMinus(this);
    }

}
