package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class BracketTerm extends BaseAstNode {

    private Term inner;

    @Nullable
    private BracketSuffixHeap suffix;

    @Nullable
    private Position position;

    public Term inner() {
        return inner;
    }

    public BracketTerm setInner(Term value) {
        inner = value;
        return this;
    }

    @Nullable()
    public BracketSuffixHeap suffix() {
        return suffix;
    }

    public BracketTerm setSuffix(@Nullable() BracketSuffixHeap value) {
        suffix = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public BracketTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public BracketTerm(Term inner, @Nullable BracketSuffixHeap suffix, @Nullable Position position) {
        this.inner = Objects.requireNonNull(inner);
        this.suffix = suffix;
        this.position = position;
    }

    public BracketTerm(Term inner) {
        this.inner = Objects.requireNonNull(inner);
        this.suffix = null;
        this.position = null;
    }

    public BracketTerm(BracketTerm other) {
        this(other.inner, other.suffix, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term inner;

        @Nullable()
        public BracketSuffixHeap suffix;

        @Nullable()
        public Position position;

        public BracketTerm build() {
            return new BracketTerm(inner, suffix, position);
        }

        public Builder inner(Term inner) {
            this.inner = inner;
            return this;
        }

        public Builder suffix(BracketSuffixHeap suffix) {
            this.suffix = suffix;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.inner = inner;
        b.suffix = suffix;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof BracketTerm that))
            return false;
        return Objects.equals(inner, that.inner) && Objects.equals(suffix, that.suffix) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "BracketTerm[inner=%s, suffix=%s, position=%s]".formatted(inner, suffix, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(inner, suffix, position);
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
