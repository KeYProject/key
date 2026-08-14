/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.BinaryAssignment.BinaryAssignmentKind;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.java.ast.expression.BinaryAssignment.BinaryAssignmentKind.COPY;


/**
 * An assignment operator of arity two.
 */
@NullMarked
public final class BinaryAssignment extends Operator
        implements Assignment<BinaryAssignmentKind> {
    public enum BinaryAssignmentKind implements AssignmentKind {
        COPY(""),
        BINARY_OR("|"),
        DIVIDE("/"),
        SHIFT_LEFT("<<"),
        UNSIGNED_SHIFT_RIGHT(">>>"),
        PLUS("+"),
        SHIFT_RIGHT(">>"),
        MINUS("-"),
        MODULO("%"),
        TIMES("*"),
        BINARY_AND("&"),
        BINARY_XOR("^");

        public final String symbol;

        BinaryAssignmentKind(String symbol) {
            this.symbol = symbol;
        }
    }

    private final BinaryAssignmentKind kind;

    public BinaryAssignment(BinaryAssignmentKind kind, ExtList changeList) {
        super(changeList);
        this.kind = Objects.requireNonNull(kind);
    }


    public BinaryAssignment(BinaryAssignmentKind kind, Expression lhs, Expression rhs) {
        super(lhs, rhs);
        this.kind = Objects.requireNonNull(kind);
    }

    public BinaryAssignment(Expression lhs, Expression rhs) {
        this(COPY, lhs, rhs);
    }


    public BinaryAssignment(PositionInfo pi, List<Comment> c, BinaryAssignmentKind kind,
            Expression target,
            Expression expr) {
        super(pi, c, new ImmutableArray<>(target, expr));
        this.kind = Objects.requireNonNull(kind);
    }

    @Override
    public boolean isLeftAssociative() {
        return false;
    }


    @Override
    public @Nullable MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (src instanceof Assignment other) {
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
        v.performActionOnBinaryAssignment(this);
    }


    @Override
    public int getArity() {
        return 2;
    }

    @Override
    public int getPrecedence() {
        return 13;
    }

    @Override
    public int getNotation() {
        return INFIX;
    }

    public BinaryAssignmentKind getKind() {
        return kind;
    }

    /**
     * overriden from Operator
     */
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
        if (!(o instanceof BinaryAssignment that))
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
