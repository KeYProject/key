package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OneInclude extends BaseAstNode {

    private String value;

    private boolean isAbsolute;

    @Nullable
    private Position position;

    public String value() {
        return value;
    }

    public OneInclude setValue(String value) {
        value = value;
        return this;
    }

    public boolean isAbsolute() {
        return isAbsolute;
    }

    public OneInclude setIsAbsolute(boolean value) {
        isAbsolute = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OneInclude setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OneInclude(String value, boolean isAbsolute, @Nullable Position position) {
        this.value = Objects.requireNonNull(value);
        this.isAbsolute = Objects.requireNonNull(isAbsolute);
        this.position = position;
    }

    public OneInclude(String value, boolean isAbsolute) {
        this.value = Objects.requireNonNull(value);
        this.isAbsolute = Objects.requireNonNull(isAbsolute);
        this.position = null;
    }

    public OneInclude(OneInclude other) {
        this(other.value, other.isAbsolute, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String value;

        @Nullable()
        public boolean isAbsolute;

        @Nullable()
        public Position position;

        public OneInclude build() {
            return new OneInclude(value, isAbsolute, position);
        }

        public Builder value(String value) {
            this.value = value;
            return this;
        }

        public Builder isAbsolute(boolean isAbsolute) {
            this.isAbsolute = isAbsolute;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.value = value;
        b.isAbsolute = isAbsolute;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OneInclude that))
            return false;
        return Objects.equals(value, that.value) && Objects.equals(isAbsolute, that.isAbsolute) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OneInclude[value=%s, isAbsolute=%s, position=%s]".formatted(value, isAbsolute, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(value, isAbsolute, position);
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
