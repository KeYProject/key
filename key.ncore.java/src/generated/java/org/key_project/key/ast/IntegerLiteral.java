package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class IntegerLiteral extends BaseAstNode implements Literals {

    private String value;

    @Nullable
    private Position position;

    public String value() {
        return value;
    }

    public IntegerLiteral setValue(String value) {
        value = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public IntegerLiteral setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public IntegerLiteral(String value, @Nullable Position position) {
        this.value = Objects.requireNonNull(value);
        this.position = position;
    }

    public IntegerLiteral(String value) {
        this.value = Objects.requireNonNull(value);
        this.position = null;
    }

    public IntegerLiteral(IntegerLiteral other) {
        this(other.value, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String value;

        @Nullable()
        public Position position;

        public IntegerLiteral build() {
            return new IntegerLiteral(value, position);
        }

        public Builder value(String value) {
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
        if (!(o instanceof IntegerLiteral that))
            return false;
        return Objects.equals(value, that.value) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "IntegerLiteral[value=%s, position=%s]".formatted(value, position);
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
