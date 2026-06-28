package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class StrongArithTerm1 extends BaseAstNode {

    enum Op {

        MUL, DIV, MOD
    }

    private Term operand;

    private Op operator;

    @Nullable
    private Position position;

    public Term operand() {
        return operand;
    }

    public StrongArithTerm1 setOperand(Term value) {
        operand = value;
        return this;
    }

    public Op operator() {
        return operator;
    }

    public StrongArithTerm1 setOperator(Op value) {
        operator = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public StrongArithTerm1 setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public StrongArithTerm1(Term operand, Op operator, @Nullable Position position) {
        this.operand = Objects.requireNonNull(operand);
        this.operator = Objects.requireNonNull(operator);
        this.position = position;
    }

    public StrongArithTerm1(Term operand, Op operator) {
        this.operand = Objects.requireNonNull(operand);
        this.operator = Objects.requireNonNull(operator);
        this.position = null;
    }

    public StrongArithTerm1(StrongArithTerm1 other) {
        this(other.operand, other.operator, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term operand;

        @Nullable()
        public Op operator;

        @Nullable()
        public Position position;

        public StrongArithTerm1 build() {
            return new StrongArithTerm1(operand, operator, position);
        }

        public Builder operand(Term operand) {
            this.operand = operand;
            return this;
        }

        public Builder operator(Op operator) {
            this.operator = operator;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.operand = operand;
        b.operator = operator;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof StrongArithTerm1 that))
            return false;
        return Objects.equals(operand, that.operand) && Objects.equals(operator, that.operator) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "StrongArithTerm1[operand=%s, operator=%s, position=%s]".formatted(operand, operator, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(operand, operator, position);
    }

    public <R> R accept(org.key_project.key.ast.visitor.Visitor<R> visitor) {
        return visitor.visit(this);
    }

    public <R, A> R accept(org.key_project.key.ast.visitor.ArgVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public void accept(org.key_project.key.ast.visitor.VoidVisitor visitor) {
        visitor.visit(this);
    }
}
