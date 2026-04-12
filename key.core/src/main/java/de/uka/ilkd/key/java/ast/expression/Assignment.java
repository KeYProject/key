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
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.expression.operator.LogicFunctionalOperator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import de.uka.ilkd.key.rule.MatchConditions;
import org.jspecify.annotations.Nullable;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;

import static de.uka.ilkd.key.java.ast.expression.Assignment.AssignmentKind.COPY;


/**
 * An assignment is an operator with side-effects.
 */
@NullMarked
public final class Assignment extends Operator implements ExpressionStatement {
    @Override
    public void visit(Visitor v) {
        v.performActionOnAssignment(this);
    }

    public AssignmentKind getKind() {
        return kind;
    }

    public enum AssignmentKind {
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

        AssignmentKind(String symbol) {
            this.symbol = symbol;
        }
    }

    private final AssignmentKind kind;

    public Assignment(ExtList children) {
        super(children);
        kind = children.get(AssignmentKind.class);
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

    public Assignment(AssignmentKind kind, Expression lhs, Expression rhs) {
        super(lhs, rhs);
        this.kind = kind;
    }

    public Assignment(Expression lhs, Expression rhs) {
        this(COPY, lhs, rhs);
    }


    public Assignment(PositionInfo pi, List<Comment> c, AssignmentKind kind, Expression target,
            Expression expr) {
        super(pi, c, new ImmutableArray<>(target, expr));
        this.kind = kind;
    }

    @Override
    public boolean isLeftAssociative() {
        return false;
    }


    @Override
    public @Nullable MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if(src instanceof Assignment other) {
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
        if (!(o instanceof Assignment that))
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
