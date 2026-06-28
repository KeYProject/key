package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Label extends BaseAstNode {

    private String name;

    @Nullable
    private Position position;

    public String name() {
        return name;
    }

    public Label setName(String value) {
        name = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Label setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Label(String name, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.position = position;
    }

    public Label(String name) {
        this.name = Objects.requireNonNull(name);
        this.position = null;
    }

    public Label(Label other) {
        this(other.name, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public Position position;

        public Label build() {
            return new Label(name, position);
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
        b.name = name;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Label that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Label[name=%s, position=%s]".formatted(name, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, position);
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
