package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class SimpleIdentDots extends BaseAstNode {

    private String fullName;

    @Nullable
    private Position position;

    public String fullName() {
        return fullName;
    }

    public SimpleIdentDots setFullName(String value) {
        fullName = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public SimpleIdentDots setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public SimpleIdentDots(String fullName, @Nullable Position position) {
        this.fullName = Objects.requireNonNull(fullName);
        this.position = position;
    }

    public SimpleIdentDots(String fullName) {
        this.fullName = Objects.requireNonNull(fullName);
        this.position = null;
    }

    public SimpleIdentDots(SimpleIdentDots other) {
        this(other.fullName, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String fullName;

        @Nullable()
        public Position position;

        public SimpleIdentDots build() {
            return new SimpleIdentDots(fullName, position);
        }

        public Builder fullName(String fullName) {
            this.fullName = fullName;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.fullName = fullName;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SimpleIdentDots that))
            return false;
        return Objects.equals(fullName, that.fullName) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "SimpleIdentDots[fullName=%s, position=%s]".formatted(fullName, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(fullName, position);
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
