package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Abbreviation extends BaseAstNode {

    private String name;

    private Term definition;

    @Nullable
    private Position position;

    public String name() {
        return name;
    }

    public Abbreviation setName(String value) {
        name = value;
        return this;
    }

    public Term definition() {
        return definition;
    }

    public Abbreviation setDefinition(Term value) {
        definition = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Abbreviation setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Abbreviation(String name, Term definition, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.definition = Objects.requireNonNull(definition);
        this.position = position;
    }

    public Abbreviation(String name, Term definition) {
        this.name = Objects.requireNonNull(name);
        this.definition = Objects.requireNonNull(definition);
        this.position = null;
    }

    public Abbreviation(Abbreviation other) {
        this(other.name, other.definition, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public Term definition;

        @Nullable()
        public Position position;

        public Abbreviation build() {
            return new Abbreviation(name, definition, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder definition(Term definition) {
            this.definition = definition;
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
        b.definition = definition;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Abbreviation that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(definition, that.definition) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Abbreviation[name=%s, definition=%s, position=%s]".formatted(name, definition, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, definition, position);
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
