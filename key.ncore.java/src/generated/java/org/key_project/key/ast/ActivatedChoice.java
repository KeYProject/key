package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ActivatedChoice extends BaseAstNode {

    private String category;

    private String choice;

    @Nullable
    private Position position;

    public String category() {
        return category;
    }

    public ActivatedChoice setCategory(String value) {
        category = value;
        return this;
    }

    public String choice() {
        return choice;
    }

    public ActivatedChoice setChoice(String value) {
        choice = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ActivatedChoice setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ActivatedChoice(String category, String choice, @Nullable Position position) {
        this.category = Objects.requireNonNull(category);
        this.choice = Objects.requireNonNull(choice);
        this.position = position;
    }

    public ActivatedChoice(String category, String choice) {
        this.category = Objects.requireNonNull(category);
        this.choice = Objects.requireNonNull(choice);
        this.position = null;
    }

    public ActivatedChoice(ActivatedChoice other) {
        this(other.category, other.choice, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String category;

        @Nullable()
        public String choice;

        @Nullable()
        public Position position;

        public ActivatedChoice build() {
            return new ActivatedChoice(category, choice, position);
        }

        public Builder category(String category) {
            this.category = category;
            return this;
        }

        public Builder choice(String choice) {
            this.choice = choice;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.category = category;
        b.choice = choice;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ActivatedChoice that))
            return false;
        return Objects.equals(category, that.category) && Objects.equals(choice, that.choice) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ActivatedChoice[category=%s, choice=%s, position=%s]".formatted(category, choice, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(category, choice, position);
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
