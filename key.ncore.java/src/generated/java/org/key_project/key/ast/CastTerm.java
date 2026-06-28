package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class CastTerm extends BaseAstNode {

    private SortId targetType;

    private Term operand;

    @Nullable
    private Position position;

    public SortId targetType() {
        return targetType;
    }

    public CastTerm setTargetType(SortId value) {
        targetType = value;
        return this;
    }

    public Term operand() {
        return operand;
    }

    public CastTerm setOperand(Term value) {
        operand = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public CastTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public CastTerm(SortId targetType, Term operand, @Nullable Position position) {
        this.targetType = Objects.requireNonNull(targetType);
        this.operand = Objects.requireNonNull(operand);
        this.position = position;
    }

    public CastTerm(SortId targetType, Term operand) {
        this.targetType = Objects.requireNonNull(targetType);
        this.operand = Objects.requireNonNull(operand);
        this.position = null;
    }

    public CastTerm(CastTerm other) {
        this(other.targetType, other.operand, other.position);
    }

    public final static class Builder {

        @Nullable()
        public SortId targetType;

        @Nullable()
        public Term operand;

        @Nullable()
        public Position position;

        public CastTerm build() {
            return new CastTerm(targetType, operand, position);
        }

        public Builder targetType(SortId targetType) {
            this.targetType = targetType;
            return this;
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
        b.targetType = targetType;
        b.operand = operand;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof CastTerm that))
            return false;
        return Objects.equals(targetType, that.targetType) && Objects.equals(operand, that.operand) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "CastTerm[targetType=%s, operand=%s, position=%s]".formatted(targetType, operand, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(targetType, operand, position);
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
