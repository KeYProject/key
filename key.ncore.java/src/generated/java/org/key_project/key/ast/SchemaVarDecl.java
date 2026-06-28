package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class SchemaVarDecl extends BaseAstNode {

    private String name;

    private String kind;

    @Nullable
    private Position position;

    public String name() {
        return name;
    }

    public SchemaVarDecl setName(String value) {
        name = value;
        return this;
    }

    public String kind() {
        return kind;
    }

    public SchemaVarDecl setKind(String value) {
        kind = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public SchemaVarDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public SchemaVarDecl(String name, String kind, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.kind = Objects.requireNonNull(kind);
        this.position = position;
    }

    public SchemaVarDecl(String name, String kind) {
        this.name = Objects.requireNonNull(name);
        this.kind = Objects.requireNonNull(kind);
        this.position = null;
    }

    public SchemaVarDecl(SchemaVarDecl other) {
        this(other.name, other.kind, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public String kind;

        @Nullable()
        public Position position;

        public SchemaVarDecl build() {
            return new SchemaVarDecl(name, kind, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder kind(String kind) {
            this.kind = kind;
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
        b.kind = kind;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SchemaVarDecl that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(kind, that.kind) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "SchemaVarDecl[name=%s, kind=%s, position=%s]".formatted(name, kind, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, kind, position);
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
