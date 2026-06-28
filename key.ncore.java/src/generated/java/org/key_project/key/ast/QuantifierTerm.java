package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class QuantifierTerm extends BaseAstNode {

    private boolean isUniversal;

    private BoundVariables variables;

    private Term body;

    @Nullable
    private Position position;

    public boolean isUniversal() {
        return isUniversal;
    }

    public QuantifierTerm setIsUniversal(boolean value) {
        isUniversal = value;
        return this;
    }

    public BoundVariables variables() {
        return variables;
    }

    public QuantifierTerm setVariables(BoundVariables value) {
        variables = value;
        return this;
    }

    public Term body() {
        return body;
    }

    public QuantifierTerm setBody(Term value) {
        body = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public QuantifierTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public QuantifierTerm(boolean isUniversal, BoundVariables variables, Term body, @Nullable Position position) {
        this.isUniversal = Objects.requireNonNull(isUniversal);
        this.variables = Objects.requireNonNull(variables);
        this.body = Objects.requireNonNull(body);
        this.position = position;
    }

    public QuantifierTerm(boolean isUniversal, BoundVariables variables, Term body) {
        this.isUniversal = Objects.requireNonNull(isUniversal);
        this.variables = Objects.requireNonNull(variables);
        this.body = Objects.requireNonNull(body);
        this.position = null;
    }

    public QuantifierTerm(QuantifierTerm other) {
        this(other.isUniversal, other.variables, other.body, other.position);
    }

    public final static class Builder {

        @Nullable()
        public boolean isUniversal;

        @Nullable()
        public BoundVariables variables;

        @Nullable()
        public Term body;

        @Nullable()
        public Position position;

        public QuantifierTerm build() {
            return new QuantifierTerm(isUniversal, variables, body, position);
        }

        public Builder isUniversal(boolean isUniversal) {
            this.isUniversal = isUniversal;
            return this;
        }

        public Builder variables(BoundVariables variables) {
            this.variables = variables;
            return this;
        }

        public Builder body(Term body) {
            this.body = body;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.isUniversal = isUniversal;
        b.variables = variables;
        b.body = body;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof QuantifierTerm that))
            return false;
        return Objects.equals(isUniversal, that.isUniversal) && Objects.equals(variables, that.variables) && Objects.equals(body, that.body) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "QuantifierTerm[isUniversal=%s, variables=%s, body=%s, position=%s]".formatted(isUniversal, variables, body, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(isUniversal, variables, body, position);
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
