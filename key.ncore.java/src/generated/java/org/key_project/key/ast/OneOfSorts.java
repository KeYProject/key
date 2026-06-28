package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OneOfSorts extends BaseAstNode {

    private List<SortId> sortIds;

    @Nullable
    private Position position;

    public List<SortId> sortIds() {
        return sortIds;
    }

    public OneOfSorts setSortIds(List<SortId> value) {
        sortIds = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OneOfSorts setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OneOfSorts(List<SortId> sortIds, @Nullable Position position) {
        this.sortIds = Objects.requireNonNull(sortIds);
        this.position = position;
    }

    public OneOfSorts(List<SortId> sortIds) {
        this.sortIds = Objects.requireNonNull(sortIds);
        this.position = null;
    }

    public OneOfSorts(OneOfSorts other) {
        this(other.sortIds, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<SortId> sortIds;

        @Nullable()
        public Position position;

        public OneOfSorts build() {
            return new OneOfSorts(sortIds, position);
        }

        public Builder sortIds(List<SortId> sortIds) {
            this.sortIds = sortIds;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder sortIds(SortId sortIds) {
            if (this.sortIds == null)
                this.sortIds = new ArrayList<>();
            this.sortIds.add(sortIds);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.sortIds = sortIds;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OneOfSorts that))
            return false;
        return Objects.equals(sortIds, that.sortIds) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OneOfSorts[sortIds=%s, position=%s]".formatted(sortIds, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(sortIds, position);
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
