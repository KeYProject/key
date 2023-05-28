package de.uka.ilkd.key.java.expression.operator.adt;

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

import java.util.List;

/**
 * Represents a function giving the length of a sequence.
 *
 * @author bruns
 * @since 1.7.2120
 *
 */
public class SeqLength extends Operator {


    public SeqLength(PositionInfo pi, List<Comment> c, Expression child) {
        super(pi, c, new ImmutableArray<>(child));
    }

    public SeqLength(ExtList changeList) {
        super(changeList);
    }


    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnSeqLength(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
    }


    @Override
    public int getNotation() {
        return Operator.PREFIX;
    }

}
