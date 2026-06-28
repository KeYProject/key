package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class SubstitutionTerm extends BaseAstNode {

    private Term term;

    private Term substitution;

    @Nullable
    private Position position;

    public Term term() {
        return term;
    }

    public SubstitutionTerm setTerm(Term value) {
        term = value;
        return this;
    }

    public Term substitution() {
        return substitution;
    }

    public SubstitutionTerm setSubstitution(Term value) {
        substitution = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public SubstitutionTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public SubstitutionTerm(Term term, Term substitution, @Nullable Position position) {
        this.term = Objects.requireNonNull(term);
        this.substitution = Objects.requireNonNull(substitution);
        this.position = position;
    }

    public SubstitutionTerm(Term term, Term substitution) {
        this.term = Objects.requireNonNull(term);
        this.substitution = Objects.requireNonNull(substitution);
        this.position = null;
    }

    public SubstitutionTerm(SubstitutionTerm other) {
        this(other.term, other.substitution, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term term;

        @Nullable()
        public Term substitution;

        @Nullable()
        public Position position;

        public SubstitutionTerm build() {
            return new SubstitutionTerm(term, substitution, position);
        }

        public Builder term(Term term) {
            this.term = term;
            return this;
        }

        public Builder substitution(Term substitution) {
            this.substitution = substitution;
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
        b.substitution = substitution;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SubstitutionTerm that))
            return false;
        return Objects.equals(term, that.term) && Objects.equals(substitution, that.substitution) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "SubstitutionTerm[term=%s, substitution=%s, position=%s]".formatted(term, substitution, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(term, substitution, position);
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
