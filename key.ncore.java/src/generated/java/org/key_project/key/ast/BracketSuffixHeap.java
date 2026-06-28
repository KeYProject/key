package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class BracketSuffixHeap extends BaseAstNode {

    private java.util.List<Term> indices;

    @Nullable
    private Position position;

    public java.util.List<Term> indices() {
        return indices;
    }

    public BracketSuffixHeap setIndices(java.util.List<Term> value) {
        indices = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public BracketSuffixHeap setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public BracketSuffixHeap(java.util.List<Term> indices, @Nullable Position position) {
        this.indices = Objects.requireNonNull(indices);
        this.position = position;
    }

    public BracketSuffixHeap(java.util.List<Term> indices) {
        this.indices = Objects.requireNonNull(indices);
        this.position = null;
    }

    public BracketSuffixHeap(BracketSuffixHeap other) {
        this(other.indices, other.position);
    }

    public final static class Builder {

        @Nullable()
        public java.util.List<Term> indices;

        @Nullable()
        public Position position;

        public BracketSuffixHeap build() {
            return new BracketSuffixHeap(indices, position);
        }

        public Builder indices(java.util.List<Term> indices) {
            this.indices = indices;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder indices(Term indices) {
            if (this.indices == null)
                this.indices = new ArrayList<>();
            this.indices.add(indices);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.indices = indices;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof BracketSuffixHeap that))
            return false;
        return Objects.equals(indices, that.indices) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "BracketSuffixHeap[indices=%s, position=%s]".formatted(indices, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(indices, position);
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
