package de.uka.ilkd.key.java.expression.operator;

import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Operator of arity 2
 *
 * @author AL
 */
public abstract class BinaryOperator extends Operator {

    public BinaryOperator(ExtList children) {
        super(children);
    }

    public BinaryOperator(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public BinaryOperator(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, new ImmutableArray<>(lhs, rhs));
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */
    public int getArity() {
        return 2;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        final TypeConverter tc = javaServ.getTypeConverter();
        try {
            return tc.getPromotedType(tc.getKeYJavaType((Expression) getChildAt(0), ec),
                tc.getKeYJavaType((Expression) getChildAt(1), ec));
        } catch (Exception e) {
            throw new RuntimeException("Type promotion failed (see below). Operator was " + this,
                e);
        }
    }

}
