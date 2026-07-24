package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class BoundVariables extends BaseAstNode {

    private List<OneBoundVariable> variables;

    @Nullable
    private Position position;

    public List<OneBoundVariable> variables() {
        return variables;
    }

    public BoundVariables setVariables(List<OneBoundVariable> value) {
        variables = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public BoundVariables setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public BoundVariables(List<OneBoundVariable> variables, @Nullable Position position) {
        this.variables = Objects.requireNonNull(variables);
        this.position = position;
    }

    public BoundVariables(List<OneBoundVariable> variables) {
        this.variables = Objects.requireNonNull(variables);
        this.position = null;
    }

    public BoundVariables(BoundVariables other) {
        this(other.variables, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<OneBoundVariable> variables;

        @Nullable()
        public Position position;

        public BoundVariables build() {
            return new BoundVariables(variables, position);
        }

        public Builder variables(List<OneBoundVariable> variables) {
            this.variables = variables;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder variables(OneBoundVariable variables) {
            if (this.variables == null)
                this.variables = new ArrayList<>();
            this.variables.add(variables);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.variables = variables;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof BoundVariables that))
            return false;
        return Objects.equals(variables, that.variables) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "BoundVariables[variables=%s, position=%s]".formatted(variables, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(variables, position);
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
