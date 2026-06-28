package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class BooleanLiteral extends BaseAstNode implements Literals {

    private boolean value;

    @Nullable
    private Position position;

    public boolean value() {
        return value;
    }

    public BooleanLiteral setValue(boolean value) {
        value = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public BooleanLiteral setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public BooleanLiteral(boolean value, @Nullable Position position) {
        this.value = Objects.requireNonNull(value);
        this.position = position;
    }

    public BooleanLiteral(boolean value) {
        this.value = Objects.requireNonNull(value);
        this.position = null;
    }

    public BooleanLiteral(BooleanLiteral other) {
        this(other.value, other.position);
    }

    public final static class Builder {

        @Nullable()
        public boolean value;

        @Nullable()
        public Position position;

        public BooleanLiteral build() {
            return new BooleanLiteral(value, position);
        }

        public Builder value(boolean value) {
            this.value = value;
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
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof BooleanLiteral that))
            return false;
        return Objects.equals(value, that.value) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "BooleanLiteral[value=%s, position=%s]".formatted(value, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(value, position);
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
