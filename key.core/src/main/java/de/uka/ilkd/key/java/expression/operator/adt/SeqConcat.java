package de.uka.ilkd.key.java.expression.operator.adt;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

public class SeqConcat extends BinaryOperator {

    public SeqConcat(PositionInfo pi, List<Comment> c, Expression child, Expression b) {
        super(pi, c, child, b);
    }

    public SeqConcat(Expression seq1, Expression seq2) {
        super(seq1, seq2);
    }

    public SeqConcat(ExtList changeList) {
        super(changeList);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnSeqConcat(this);
    }

}
