package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OneInvariant extends BaseAstNode {

    private String name;

    private Term formula;

    @Nullable
    private String displayName;

    @Nullable
    private Position position;

    public String name() {
        return name;
    }

    public OneInvariant setName(String value) {
        name = value;
        return this;
    }

    public Term formula() {
        return formula;
    }

    public OneInvariant setFormula(Term value) {
        formula = value;
        return this;
    }

    @Nullable()
    public String displayName() {
        return displayName;
    }

    public OneInvariant setDisplayName(@Nullable() String value) {
        displayName = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OneInvariant setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OneInvariant(String name, Term formula, @Nullable String displayName, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.formula = Objects.requireNonNull(formula);
        this.displayName = displayName;
        this.position = position;
    }

    public OneInvariant(String name, Term formula) {
        this.name = Objects.requireNonNull(name);
        this.formula = Objects.requireNonNull(formula);
        this.displayName = null;
        this.position = null;
    }

    public OneInvariant(OneInvariant other) {
        this(other.name, other.formula, other.displayName, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public Term formula;

        @Nullable()
        public String displayName;

        @Nullable()
        public Position position;

        public OneInvariant build() {
            return new OneInvariant(name, formula, displayName, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder formula(Term formula) {
            this.formula = formula;
            return this;
        }

        public Builder displayName(String displayName) {
            this.displayName = displayName;
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
        b.displayName = displayName;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OneInvariant that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(formula, that.formula) && Objects.equals(displayName, that.displayName) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OneInvariant[name=%s, formula=%s, displayName=%s, position=%s]".formatted(name, formula, displayName, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, formula, displayName, position);
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
