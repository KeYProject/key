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
import de.uka.ilkd.key.java.ast.expression.ExpressionStatement;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/12/26)
 */
public final class UnaryOperator extends Operator implements ExpressionStatement {
    public UnaryOperator(UnaryOperatorKind kind, Expression arg) {
        super(arg);
        this.kind = Objects.requireNonNull(kind);
    }

    public final UnaryOperatorKind kind;

    public UnaryOperator(PositionInfo pi, List<Comment> c, UnaryOperatorKind op, Expression child) {
        super(pi, c, new ImmutableArray<>(child));
        this.kind = Objects.requireNonNull(op);
    }

    public UnaryOperator(UnaryOperatorKind kind, ExtList changeList) {
        super(changeList);
        this.kind = Objects.requireNonNull(kind);
    }

    public UnaryOperatorKind getKind() {
        return kind;
    }

    @Override
    public int getArity() {
        return 1;
    }

    @Override
    public int getPrecedence() {
        return kind.precedence;
    }

    @Override
    public int getNotation() {
        return kind.notation;
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (src instanceof UnaryOperator other) {
            if (this.kind.equals(other.getKind())) {
                return super.match(source, matchCond);
            }
        }
        return null;
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        final TypeConverter tc = javaServ.getTypeConverter();

        try {
            return switch (kind) {
                case LOGICAL_NOT -> javaServ.getTypeConverter().getBooleanType();
                case POST_DECREMENT, POST_INCREMENT,
                        PRE_DECREMENT, PRE_INCREMENT ->
                    tc.getKeYJavaType((Expression) getChildAt(0), ec);
                default -> tc.getPromotedType(tc.getKeYJavaType((Expression) getChildAt(0), ec));
            };
        } catch (Exception e) {
            throw new RuntimeException("Type promotion failed (see below). Operator was " + this,
                e);
        }
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnUnaryOperator(this);
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof UnaryOperator that))
            return false;
        if (!super.equals(o))
            return false;
        return kind == that.kind && Objects.equals(that.children, children);
    }

    @Override
    protected int computeHashCode() {
        return Objects.hash(kind, children);
    }
}
