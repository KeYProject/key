package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ProofScriptParameter extends BaseAstNode {

    @Nullable
    private String name;

    private Object expression;

    @Nullable
    private Position position;

    @Nullable()
    public String name() {
        return name;
    }

    public ProofScriptParameter setName(@Nullable() String value) {
        name = value;
        return this;
    }

    public Object expression() {
        return expression;
    }

    public ProofScriptParameter setExpression(Object value) {
        expression = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ProofScriptParameter setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ProofScriptParameter(@Nullable String name, Object expression, @Nullable Position position) {
        this.name = name;
        this.expression = Objects.requireNonNull(expression);
        this.position = position;
    }

    public ProofScriptParameter(Object expression) {
        this.name = null;
        this.expression = Objects.requireNonNull(expression);
        this.position = null;
    }

    public ProofScriptParameter(ProofScriptParameter other) {
        this(other.name, other.expression, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public Object expression;

        @Nullable()
        public Position position;

        public ProofScriptParameter build() {
            return new ProofScriptParameter(name, expression, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder expression(Object expression) {
            this.expression = expression;
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
        b.expression = expression;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ProofScriptParameter that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(expression, that.expression) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ProofScriptParameter[name=%s, expression=%s, position=%s]".formatted(name, expression, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, expression, position);
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
