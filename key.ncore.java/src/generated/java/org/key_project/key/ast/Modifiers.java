package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Modifiers extends BaseAstNode {

    private List<String> modifierNames;

    @Nullable
    private Position position;

    public List<String> modifierNames() {
        return modifierNames;
    }

    public Modifiers setModifierNames(List<String> value) {
        modifierNames = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Modifiers setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Modifiers(List<String> modifierNames, @Nullable Position position) {
        this.modifierNames = Objects.requireNonNull(modifierNames);
        this.position = position;
    }

    public Modifiers(List<String> modifierNames) {
        this.modifierNames = Objects.requireNonNull(modifierNames);
        this.position = null;
    }

    public Modifiers(Modifiers other) {
        this(other.modifierNames, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<String> modifierNames;

        @Nullable()
        public Position position;

        public Modifiers build() {
            return new Modifiers(modifierNames, position);
        }

        public Builder modifierNames(List<String> modifierNames) {
            this.modifierNames = modifierNames;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder modifierNames(String modifierNames) {
            if (this.modifierNames == null)
                this.modifierNames = new ArrayList<>();
            this.modifierNames.add(modifierNames);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.modifierNames = modifierNames;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Modifiers that))
            return false;
        return Objects.equals(modifierNames, that.modifierNames) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Modifiers[modifierNames=%s, position=%s]".formatted(modifierNames, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(modifierNames, position);
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
