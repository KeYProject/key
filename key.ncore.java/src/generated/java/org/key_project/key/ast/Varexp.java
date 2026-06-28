package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Varexp extends BaseAstNode {

    private String name;

    private KeyJavaType type;

    @Nullable
    private Position position;

    public String name() {
        return name;
    }

    public Varexp setName(String value) {
        name = value;
        return this;
    }

    public KeyJavaType type() {
        return type;
    }

    public Varexp setType(KeyJavaType value) {
        type = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Varexp setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Varexp(String name, KeyJavaType type, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.type = Objects.requireNonNull(type);
        this.position = position;
    }

    public Varexp(String name, KeyJavaType type) {
        this.name = Objects.requireNonNull(name);
        this.type = Objects.requireNonNull(type);
        this.position = null;
    }

    public Varexp(Varexp other) {
        this(other.name, other.type, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public KeyJavaType type;

        @Nullable()
        public Position position;

        public Varexp build() {
            return new Varexp(name, type, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder type(KeyJavaType type) {
            this.type = type;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.name = name;
        b.type = type;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Varexp that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(type, that.type) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Varexp[name=%s, type=%s, position=%s]".formatted(name, type, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, type, position);
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
