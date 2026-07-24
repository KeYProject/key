package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ReplaceWith extends BaseAstNode {

    @Nullable
    private Term term;

    @Nullable
    private Seq antecedent;

    @Nullable
    private Seq succulent;

    @Nullable
    private Position position;

    @Nullable()
    public Term term() {
        return term;
    }

    public ReplaceWith setTerm(@Nullable() Term value) {
        term = value;
        return this;
    }

    @Nullable()
    public Seq antecedent() {
        return antecedent;
    }

    public ReplaceWith setAntecedent(@Nullable() Seq value) {
        antecedent = value;
        return this;
    }

    @Nullable()
    public Seq succulent() {
        return succulent;
    }

    public ReplaceWith setSucculent(@Nullable() Seq value) {
        succulent = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ReplaceWith setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ReplaceWith(@Nullable Term term, @Nullable Seq antecedent, @Nullable Seq succulent, @Nullable Position position) {
        this.term = term;
        this.antecedent = antecedent;
        this.succulent = succulent;
        this.position = position;
    }

    public ReplaceWith() {
        this.term = null;
        this.antecedent = null;
        this.succulent = null;
        this.position = null;
    }

    public ReplaceWith(ReplaceWith other) {
        this(other.term, other.antecedent, other.succulent, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term term;

        @Nullable()
        public Seq antecedent;

        @Nullable()
        public Seq succulent;

        @Nullable()
        public Position position;

        public ReplaceWith build() {
            return new ReplaceWith(term, antecedent, succulent, position);
        }

        public Builder term(Term term) {
            this.term = term;
            return this;
        }

        public Builder antecedent(Seq antecedent) {
            this.antecedent = antecedent;
            return this;
        }

        public Builder succulent(Seq succulent) {
            this.succulent = succulent;
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
        b.antecedent = antecedent;
        b.succulent = succulent;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ReplaceWith that))
            return false;
        return Objects.equals(term, that.term) && Objects.equals(antecedent, that.antecedent) && Objects.equals(succulent, that.succulent) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ReplaceWith[term=%s, antecedent=%s, succulent=%s, position=%s]".formatted(term, antecedent, succulent, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(term, antecedent, succulent, position);
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
