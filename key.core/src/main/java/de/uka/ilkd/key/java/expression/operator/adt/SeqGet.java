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

import org.key_project.util.collection.ImmutableArray;

/**
 * Represents a sequence getter function.
 *
 * @author bruns
 * @since 1.7.2120
 */
public class SeqGet extends Operator {

    public SeqGet(PositionInfo pi, List<Comment> c, Expression child, Expression b) {
        super(pi, c, new ImmutableArray<>(child, b));
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnSeqGet(this);
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
