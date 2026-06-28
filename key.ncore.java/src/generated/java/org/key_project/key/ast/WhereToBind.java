package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class WhereToBind extends BaseAstNode {

    private List<Boolean> bindValues;

    @Nullable
    private Position position;

    public List<Boolean> bindValues() {
        return bindValues;
    }

    public WhereToBind setBindValues(List<Boolean> value) {
        bindValues = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public WhereToBind setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public WhereToBind(List<Boolean> bindValues, @Nullable Position position) {
        this.bindValues = Objects.requireNonNull(bindValues);
        this.position = position;
    }

    public WhereToBind(List<Boolean> bindValues) {
        this.bindValues = Objects.requireNonNull(bindValues);
        this.position = null;
    }

    public WhereToBind(WhereToBind other) {
        this(other.bindValues, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<Boolean> bindValues;

        @Nullable()
        public Position position;

        public WhereToBind build() {
            return new WhereToBind(bindValues, position);
        }

        public Builder bindValues(List<Boolean> bindValues) {
            this.bindValues = bindValues;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder bindValues(Boolean bindValues) {
            if (this.bindValues == null)
                this.bindValues = new ArrayList<>();
            this.bindValues.add(bindValues);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.bindValues = bindValues;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof WhereToBind that))
            return false;
        return Objects.equals(bindValues, that.bindValues) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "WhereToBind[bindValues=%s, position=%s]".formatted(bindValues, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(bindValues, position);
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
