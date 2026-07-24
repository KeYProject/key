package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OneBoundVariable extends BaseAstNode {

    @Nullable
    private SortId sort;

    private String name;

    @Nullable
    private Position position;

    @Nullable()
    public SortId sort() {
        return sort;
    }

    public OneBoundVariable setSort(@Nullable() SortId value) {
        sort = value;
        return this;
    }

    public String name() {
        return name;
    }

    public OneBoundVariable setName(String value) {
        name = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OneBoundVariable setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OneBoundVariable(@Nullable SortId sort, String name, @Nullable Position position) {
        this.sort = sort;
        this.name = Objects.requireNonNull(name);
        this.position = position;
    }

    public OneBoundVariable(String name) {
        this.sort = null;
        this.name = Objects.requireNonNull(name);
        this.position = null;
    }

    public OneBoundVariable(OneBoundVariable other) {
        this(other.sort, other.name, other.position);
    }

    public final static class Builder {

        @Nullable()
        public SortId sort;

        @Nullable()
        public String name;

        @Nullable()
        public Position position;

        public OneBoundVariable build() {
            return new OneBoundVariable(sort, name, position);
        }

        public Builder sort(SortId sort) {
            this.sort = sort;
            return this;
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.sort = sort;
        b.name = name;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OneBoundVariable that))
            return false;
        return Objects.equals(sort, that.sort) && Objects.equals(name, that.name) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OneBoundVariable[sort=%s, name=%s, position=%s]".formatted(sort, name, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(sort, name, position);
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
