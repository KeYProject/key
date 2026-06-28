package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Attribute extends BaseAstNode {

    private String fieldName;

    @Nullable
    private Position position;

    public String fieldName() {
        return fieldName;
    }

    public Attribute setFieldName(String value) {
        fieldName = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Attribute setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Attribute(String fieldName, @Nullable Position position) {
        this.fieldName = Objects.requireNonNull(fieldName);
        this.position = position;
    }

    public Attribute(String fieldName) {
        this.fieldName = Objects.requireNonNull(fieldName);
        this.position = null;
    }

    public Attribute(Attribute other) {
        this(other.fieldName, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String fieldName;

        @Nullable()
        public Position position;

        public Attribute build() {
            return new Attribute(fieldName, position);
        }

        public Builder fieldName(String fieldName) {
            this.fieldName = fieldName;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.fieldName = fieldName;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Attribute that))
            return false;
        return Objects.equals(fieldName, that.fieldName) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Attribute[fieldName=%s, position=%s]".formatted(fieldName, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(fieldName, position);
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
