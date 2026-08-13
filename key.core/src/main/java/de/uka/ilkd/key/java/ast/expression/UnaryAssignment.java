/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.UnaryAssignment.UnaryAssignmentKind;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * An assignment is an operator with side-effects.
 */
@NullMarked
public final class UnaryAssignment extends Operator
        implements Assignment<UnaryAssignmentKind> {
    public enum UnaryAssignmentKind implements AssignmentKind {
        PRE_INCREMENT("++", 1),
        PRE_DECREMENT("--", 1),
        POST_INCREMENT("++", 1, Operator.POSTFIX),
        POST_DECREMENT("--", 1, Operator.POSTFIX);

        public final String symbol;
        public final int precedence;
        public final int notation;


        UnaryAssignmentKind(String symbol, int precedence) {
            this(symbol, precedence, Operator.PREFIX);
        }

        UnaryAssignmentKind(String symbol, int precedence, int notation) {
            this.symbol = symbol;
            this.notation = notation;
            this.precedence = precedence;
        }
    }

    private final UnaryAssignmentKind kind;

    public UnaryAssignment(UnaryAssignmentKind kind, ExtList changeList) {
        super(changeList);
        this.kind = Objects.requireNonNull(kind);
    }

    public UnaryAssignment(UnaryAssignmentKind kind, Expression sub) {
        super(sub);
        this.kind = Objects.requireNonNull(kind);
    }

    public UnaryAssignment(PositionInfo pi, List<Comment> c, UnaryAssignmentKind kind,
            Expression sub) {
        super(pi, c, new ImmutableArray<>(sub));
        this.kind = Objects.requireNonNull(kind);
    }

    @Override
    public boolean isLeftAssociative() {
        return false;
    }


    @Override
    public @Nullable MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (src instanceof UnaryAssignment other) {
            if (getKind().equals(other.getKind())) {
                return super.match(source, matchCond);
            }
        }
        return null;
    }

    /**
     * retrieves the type of the assignment expression
     *
     * @param javaServ the Services offering access to the Java model
     * @param ec the ExecutionContext in which the expression is evaluated
     * @return the type of the assignment expression
     */
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getExpressionAt(0).getKeYJavaType(javaServ, ec);
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnUnaryAssignment(this);
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

    public UnaryAssignmentKind getKind() {
        return kind;
    }

    @Override
    public String reuseSignature(Services services, ExecutionContext ec) {
        String base = super.reuseSignature(services, ec);
        Expression rhs;
        try {
            rhs = children.get(1);
        } catch (ArrayIndexOutOfBoundsException e) {
            // no second argument, e.g. PostIncrement
            return base;
        }
        if (rhs instanceof BooleanLiteral) {
            return base + "[" + rhs + "]";
        } else {
            return base;
        }
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof UnaryAssignment that))
            return false;
        if (!super.equals(o))
            return false;
        return kind == that.kind;
    }

    @Override
    protected int computeHashCode() {
        return 0x01000193 * super.computeHashCode() + kind.hashCode();
    }
}
