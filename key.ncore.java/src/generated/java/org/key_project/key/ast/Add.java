package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Add extends BaseAstNode {

    private Term term;

    @Nullable
    private Position position;

    public Term term() {
        return term;
    }

    public Add setTerm(Term value) {
        term = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Add setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Add(Term term, @Nullable Position position) {
        this.term = Objects.requireNonNull(term);
        this.position = position;
    }

    public Add(Term term) {
        this.term = Objects.requireNonNull(term);
        this.position = null;
    }

    public Add(Add other) {
        this(other.term, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term term;

        @Nullable()
        public Position position;

        public Add build() {
            return new Add(term, position);
        }

        public Builder term(Term term) {
            this.term = term;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.term = term;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Add that))
            return false;
        return Objects.equals(term, that.term) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Add[term=%s, position=%s]".formatted(term, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(term, position);
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
