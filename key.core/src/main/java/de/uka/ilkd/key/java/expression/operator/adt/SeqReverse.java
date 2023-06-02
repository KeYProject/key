package de.uka.ilkd.key.java.expression.operator.adt;

import java.util.List;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

public class SeqReverse extends Operator {

    public SeqReverse(PositionInfo pi, List<Comment> c, Expression child) {
        super(pi, c, new ImmutableArray<>(child));
    }

    public SeqReverse(ExtList changeList) {
        super(changeList);
    }


    @Override
    public int getPrecedence() {
        return 0;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnSeqReverse(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    }
}
