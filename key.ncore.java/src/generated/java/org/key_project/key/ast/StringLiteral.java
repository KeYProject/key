package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class StringLiteral extends BaseAstNode implements Literals {

    private String value;

    @Nullable
    private Position position;

    public String value() {
        return value;
    }

    public StringLiteral setValue(String value) {
        value = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public StringLiteral setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public StringLiteral(String value, @Nullable Position position) {
        this.value = Objects.requireNonNull(value);
        this.position = position;
    }

    public StringLiteral(String value) {
        this.value = Objects.requireNonNull(value);
        this.position = null;
    }

    public StringLiteral(StringLiteral other) {
        this(other.value, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String value;

        @Nullable()
        public Position position;

        public StringLiteral build() {
            return new StringLiteral(value, position);
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
        if (!(o instanceof StringLiteral that))
            return false;
        return Objects.equals(value, that.value) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "StringLiteral[value=%s, position=%s]".formatted(value, position);
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
