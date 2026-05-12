/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import de.uka.ilkd.key.rule.MatchConditions;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

public final class BinaryOperator extends Operator {
    public BinaryOperator(BinaryOperatorKind binaryOperatorKind, ExtList operands) {
        super(operands);
        kind = binaryOperatorKind;
    }

    private final BinaryOperatorKind kind;

    public BinaryOperator(ExtList children) {
        super(children);
        kind = children.get(BinaryOperatorKind.class);
    }

    public BinaryOperator(BinaryOperatorKind kind, Expression lhs, Expression rhs) {
        super(lhs, rhs);
        this.kind = kind;
    }

    public BinaryOperator(PositionInfo pi, List<Comment> c,
            BinaryOperatorKind kind, Expression lhs, Expression rhs) {
        super(pi, c,
            new ImmutableArray<>(Objects.requireNonNull(lhs), Objects.requireNonNull(rhs)));
        this.kind = kind;
    }


    public BinaryOperatorKind getKind() {
        return kind;
    }

    public int getArity() {
        return 2;
    }

    @Override
    public int getPrecedence() {
        return kind.precedence;
    }

    @Override
    public int getNotation() {
        return INFIX;
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

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource(); // [ left, right ]
        if(src instanceof BinaryOperator other) {
            if (this.kind.equals(other.getKind())) {
                return super.match(source, matchCond);
            }
        }
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBinaryOperator(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (!(o instanceof BinaryOperator b))
            return false;
        return Objects.equals(getKind(), b.getKind()) && Objects.equals(children, b.children);
    }

    @Override
    protected int computeHashCode() {
        return Objects.hash(kind, children);
    }
}
