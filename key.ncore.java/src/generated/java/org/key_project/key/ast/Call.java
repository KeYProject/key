package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Call extends BaseAstNode {

    private java.util.List<Term> arguments;

    @Nullable
    private Position position;

    public java.util.List<Term> arguments() {
        return arguments;
    }

    public Call setArguments(java.util.List<Term> value) {
        arguments = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Call setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Call(java.util.List<Term> arguments, @Nullable Position position) {
        this.arguments = Objects.requireNonNull(arguments);
        this.position = position;
    }

    public Call(java.util.List<Term> arguments) {
        this.arguments = Objects.requireNonNull(arguments);
        this.position = null;
    }

    public Call(Call other) {
        this(other.arguments, other.position);
    }

    public final static class Builder {

        @Nullable()
        public java.util.List<Term> arguments;

        @Nullable()
        public Position position;

        public Call build() {
            return new Call(arguments, position);
        }

        public Builder arguments(java.util.List<Term> arguments) {
            this.arguments = arguments;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder arguments(Term arguments) {
            if (this.arguments == null)
                this.arguments = new ArrayList<>();
            this.arguments.add(arguments);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.arguments = arguments;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Call that))
            return false;
        return Objects.equals(arguments, that.arguments) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Call[arguments=%s, position=%s]".formatted(arguments, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(arguments, position);
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
