package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class DisjunctionTerm extends BaseAstNode {

    private Term left;

    private Term right;

    @Nullable
    private Position position;

    public Term left() {
        return left;
    }

    public DisjunctionTerm setLeft(Term value) {
        left = value;
        return this;
    }

    public Term right() {
        return right;
    }

    public DisjunctionTerm setRight(Term value) {
        right = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public DisjunctionTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public DisjunctionTerm(Term left, Term right, @Nullable Position position) {
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.position = position;
    }

    public DisjunctionTerm(Term left, Term right) {
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.position = null;
    }

    public DisjunctionTerm(DisjunctionTerm other) {
        this(other.left, other.right, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term left;

        @Nullable()
        public Term right;

        @Nullable()
        public Position position;

        public DisjunctionTerm build() {
            return new DisjunctionTerm(left, right, position);
        }

        public Builder left(Term left) {
            this.left = left;
            return this;
        }

        public Builder right(Term right) {
            this.right = right;
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
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof DisjunctionTerm that))
            return false;
        return Objects.equals(left, that.left) && Objects.equals(right, that.right) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "DisjunctionTerm[left=%s, right=%s, position=%s]".formatted(left, right, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(left, right, position);
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
