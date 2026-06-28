package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class EqualityTerm extends BaseAstNode {

    private Term left;

    private Term right;

    private boolean isEquality;

    @Nullable
    private Position position;

    public Term left() {
        return left;
    }

    public EqualityTerm setLeft(Term value) {
        left = value;
        return this;
    }

    public Term right() {
        return right;
    }

    public EqualityTerm setRight(Term value) {
        right = value;
        return this;
    }

    public boolean isEquality() {
        return isEquality;
    }

    public EqualityTerm setIsEquality(boolean value) {
        isEquality = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public EqualityTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public EqualityTerm(Term left, Term right, boolean isEquality, @Nullable Position position) {
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.isEquality = Objects.requireNonNull(isEquality);
        this.position = position;
    }

    public EqualityTerm(Term left, Term right, boolean isEquality) {
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.isEquality = Objects.requireNonNull(isEquality);
        this.position = null;
    }

    public EqualityTerm(EqualityTerm other) {
        this(other.left, other.right, other.isEquality, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term left;

        @Nullable()
        public Term right;

        @Nullable()
        public boolean isEquality;

        @Nullable()
        public Position position;

        public EqualityTerm build() {
            return new EqualityTerm(left, right, isEquality, position);
        }

        public Builder left(Term left) {
            this.left = left;
            return this;
        }

        public Builder right(Term right) {
            this.right = right;
            return this;
        }

        public Builder isEquality(boolean isEquality) {
            this.isEquality = isEquality;
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
        b.isEquality = isEquality;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof EqualityTerm that))
            return false;
        return Objects.equals(left, that.left) && Objects.equals(right, that.right) && Objects.equals(isEquality, that.isEquality) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "EqualityTerm[left=%s, right=%s, isEquality=%s, position=%s]".formatted(left, right, isEquality, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(left, right, isEquality, position);
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
