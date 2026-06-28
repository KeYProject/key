package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OneContract extends BaseAstNode {

    private String name;

    private Term formula;

    private Term modifiableClause;

    @Nullable
    private Position position;

    public String name() {
        return name;
    }

    public OneContract setName(String value) {
        name = value;
        return this;
    }

    public Term formula() {
        return formula;
    }

    public OneContract setFormula(Term value) {
        formula = value;
        return this;
    }

    public Term modifiableClause() {
        return modifiableClause;
    }

    public OneContract setModifiableClause(Term value) {
        modifiableClause = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OneContract setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OneContract(String name, Term formula, Term modifiableClause, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.formula = Objects.requireNonNull(formula);
        this.modifiableClause = Objects.requireNonNull(modifiableClause);
        this.position = position;
    }

    public OneContract(String name, Term formula, Term modifiableClause) {
        this.name = Objects.requireNonNull(name);
        this.formula = Objects.requireNonNull(formula);
        this.modifiableClause = Objects.requireNonNull(modifiableClause);
        this.position = null;
    }

    public OneContract(OneContract other) {
        this(other.name, other.formula, other.modifiableClause, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public Term formula;

        @Nullable()
        public Term modifiableClause;

        @Nullable()
        public Position position;

        public OneContract build() {
            return new OneContract(name, formula, modifiableClause, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder formula(Term formula) {
            this.formula = formula;
            return this;
        }

        public Builder modifiableClause(Term modifiableClause) {
            this.modifiableClause = modifiableClause;
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
        b.formula = formula;
        b.modifiableClause = modifiableClause;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OneContract that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(formula, that.formula) && Objects.equals(modifiableClause, that.modifiableClause) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OneContract[name=%s, formula=%s, modifiableClause=%s, position=%s]".formatted(name, formula, modifiableClause, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, formula, modifiableClause, position);
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
