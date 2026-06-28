package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class StrongArithTerm2 extends BaseAstNode {

    enum Op {

        MUL, DIV, MOD
    }

    private Term left;

    private Term right;

    private Op operator;

    @Nullable
    private Position position;

    public Term left() {
        return left;
    }

    public StrongArithTerm2 setLeft(Term value) {
        left = value;
        return this;
    }

    public Term right() {
        return right;
    }

    public StrongArithTerm2 setRight(Term value) {
        right = value;
        return this;
    }

    public Op operator() {
        return operator;
    }

    public StrongArithTerm2 setOperator(Op value) {
        operator = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public StrongArithTerm2 setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public StrongArithTerm2(Term left, Term right, Op operator, @Nullable Position position) {
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.operator = Objects.requireNonNull(operator);
        this.position = position;
    }

    public StrongArithTerm2(Term left, Term right, Op operator) {
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.operator = Objects.requireNonNull(operator);
        this.position = null;
    }

    public StrongArithTerm2(StrongArithTerm2 other) {
        this(other.left, other.right, other.operator, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term left;

        @Nullable()
        public Term right;

        @Nullable()
        public Op operator;

        @Nullable()
        public Position position;

        public StrongArithTerm2 build() {
            return new StrongArithTerm2(left, right, operator, position);
        }

        public Builder left(Term left) {
            this.left = left;
            return this;
        }

        public Builder right(Term right) {
            this.right = right;
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
        b.left = left;
        b.right = right;
        b.operator = operator;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof StrongArithTerm2 that))
            return false;
        return Objects.equals(left, that.left) && Objects.equals(right, that.right) && Objects.equals(operator, that.operator) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "StrongArithTerm2[left=%s, right=%s, operator=%s, position=%s]".formatted(left, right, operator, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(left, right, operator, position);
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
