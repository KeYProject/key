package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class NegationTerm extends BaseAstNode {

    private Term operand;

    @Nullable
    private Position position;

    public Term operand() {
        return operand;
    }

    public NegationTerm setOperand(Term value) {
        operand = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public NegationTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public NegationTerm(Term operand, @Nullable Position position) {
        this.operand = Objects.requireNonNull(operand);
        this.position = position;
    }

    public NegationTerm(Term operand) {
        this.operand = Objects.requireNonNull(operand);
        this.position = null;
    }

    public NegationTerm(NegationTerm other) {
        this(other.operand, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term operand;

        @Nullable()
        public Position position;

        public NegationTerm build() {
            return new NegationTerm(operand, position);
        }

        public Builder operand(Term operand) {
            this.operand = operand;
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
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof NegationTerm that))
            return false;
        return Objects.equals(operand, that.operand) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "NegationTerm[operand=%s, position=%s]".formatted(operand, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(operand, position);
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
