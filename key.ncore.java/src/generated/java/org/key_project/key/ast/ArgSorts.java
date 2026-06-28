package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ArgSorts extends BaseAstNode {

    private List<SortId> sorts;

    @Nullable
    private Position position;

    public List<SortId> sorts() {
        return sorts;
    }

    public ArgSorts setSorts(List<SortId> value) {
        sorts = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ArgSorts setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ArgSorts(List<SortId> sorts, @Nullable Position position) {
        this.sorts = Objects.requireNonNull(sorts);
        this.position = position;
    }

    public ArgSorts(List<SortId> sorts) {
        this.sorts = Objects.requireNonNull(sorts);
        this.position = null;
    }

    public ArgSorts(ArgSorts other) {
        this(other.sorts, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<SortId> sorts;

        @Nullable()
        public Position position;

        public ArgSorts build() {
            return new ArgSorts(sorts, position);
        }

        public Builder sorts(List<SortId> sorts) {
            this.sorts = sorts;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder sorts(SortId sorts) {
            if (this.sorts == null)
                this.sorts = new ArrayList<>();
            this.sorts.add(sorts);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.sorts = sorts;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ArgSorts that))
            return false;
        return Objects.equals(sorts, that.sorts) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ArgSorts[sorts=%s, position=%s]".formatted(sorts, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(sorts, position);
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
