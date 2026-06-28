package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class BraceSuffix extends BaseAstNode {

    private java.util.List<Term> elements;

    @Nullable
    private Position position;

    public java.util.List<Term> elements() {
        return elements;
    }

    public BraceSuffix setElements(java.util.List<Term> value) {
        elements = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public BraceSuffix setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public BraceSuffix(java.util.List<Term> elements, @Nullable Position position) {
        this.elements = Objects.requireNonNull(elements);
        this.position = position;
    }

    public BraceSuffix(java.util.List<Term> elements) {
        this.elements = Objects.requireNonNull(elements);
        this.position = null;
    }

    public BraceSuffix(BraceSuffix other) {
        this(other.elements, other.position);
    }

    public final static class Builder {

        @Nullable()
        public java.util.List<Term> elements;

        @Nullable()
        public Position position;

        public BraceSuffix build() {
            return new BraceSuffix(elements, position);
        }

        public Builder elements(java.util.List<Term> elements) {
            this.elements = elements;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder elements(Term elements) {
            if (this.elements == null)
                this.elements = new ArrayList<>();
            this.elements.add(elements);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.elements = elements;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof BraceSuffix that))
            return false;
        return Objects.equals(elements, that.elements) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "BraceSuffix[elements=%s, position=%s]".formatted(elements, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(elements, position);
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
