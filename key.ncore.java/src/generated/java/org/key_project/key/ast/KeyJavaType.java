package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class KeyJavaType extends BaseAstNode {

    private String typeName;

    @Nullable
    private Position position;

    public String typeName() {
        return typeName;
    }

    public KeyJavaType setTypeName(String value) {
        typeName = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public KeyJavaType setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public KeyJavaType(String typeName, @Nullable Position position) {
        this.typeName = Objects.requireNonNull(typeName);
        this.position = position;
    }

    public KeyJavaType(String typeName) {
        this.typeName = Objects.requireNonNull(typeName);
        this.position = null;
    }

    public KeyJavaType(KeyJavaType other) {
        this(other.typeName, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String typeName;

        @Nullable()
        public Position position;

        public KeyJavaType build() {
            return new KeyJavaType(typeName, position);
        }

        public Builder typeName(String typeName) {
            this.typeName = typeName;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.typeName = typeName;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof KeyJavaType that))
            return false;
        return Objects.equals(typeName, that.typeName) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "KeyJavaType[typeName=%s, position=%s]".formatted(typeName, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(typeName, position);
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
