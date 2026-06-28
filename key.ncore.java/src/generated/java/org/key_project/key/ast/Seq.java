package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Seq extends BaseAstNode {

    private List<Term> terms;

    @Nullable
    private Position position;

    public List<Term> terms() {
        return terms;
    }

    public Seq setTerms(List<Term> value) {
        terms = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Seq setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Seq(List<Term> terms, @Nullable Position position) {
        this.terms = Objects.requireNonNull(terms);
        this.position = position;
    }

    public Seq(List<Term> terms) {
        this.terms = Objects.requireNonNull(terms);
        this.position = null;
    }

    public Seq(Seq other) {
        this(other.terms, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<Term> terms;

        @Nullable()
        public Position position;

        public Seq build() {
            return new Seq(terms, position);
        }

        public Builder terms(List<Term> terms) {
            this.terms = terms;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder terms(Term terms) {
            if (this.terms == null)
                this.terms = new ArrayList<>();
            this.terms.add(terms);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.terms = terms;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Seq that))
            return false;
        return Objects.equals(terms, that.terms) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Seq[terms=%s, position=%s]".formatted(terms, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(terms, position);
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
