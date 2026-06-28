package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OptionDecls extends BaseAstNode {

    private List<Choice> choices;

    @Nullable
    private Position position;

    public List<Choice> choices() {
        return choices;
    }

    public OptionDecls setChoices(List<Choice> value) {
        choices = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OptionDecls setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OptionDecls(List<Choice> choices, @Nullable Position position) {
        this.choices = Objects.requireNonNull(choices);
        this.position = position;
    }

    public OptionDecls(List<Choice> choices) {
        this.choices = Objects.requireNonNull(choices);
        this.position = null;
    }

    public OptionDecls(OptionDecls other) {
        this(other.choices, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<Choice> choices;

        @Nullable()
        public Position position;

        public OptionDecls build() {
            return new OptionDecls(choices, position);
        }

        public Builder choices(List<Choice> choices) {
            this.choices = choices;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder choices(Choice choices) {
            if (this.choices == null)
                this.choices = new ArrayList<>();
            this.choices.add(choices);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.choices = choices;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OptionDecls that))
            return false;
        return Objects.equals(choices, that.choices) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OptionDecls[choices=%s, position=%s]".formatted(choices, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(choices, position);
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
