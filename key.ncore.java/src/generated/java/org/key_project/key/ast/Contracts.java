package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Contracts extends BaseAstNode {

    private List<RulesOrAxioms> items;

    @Nullable
    private Position position;

    public List<RulesOrAxioms> items() {
        return items;
    }

    public Contracts setItems(List<RulesOrAxioms> value) {
        items = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Contracts setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Contracts(List<RulesOrAxioms> items, @Nullable Position position) {
        this.items = Objects.requireNonNull(items);
        this.position = position;
    }

    public Contracts(List<RulesOrAxioms> items) {
        this.items = Objects.requireNonNull(items);
        this.position = null;
    }

    public Contracts(Contracts other) {
        this(other.items, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<RulesOrAxioms> items;

        @Nullable()
        public Position position;

        public Contracts build() {
            return new Contracts(items, position);
        }

        public Builder items(List<RulesOrAxioms> items) {
            this.items = items;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder items(RulesOrAxioms items) {
            if (this.items == null)
                this.items = new ArrayList<>();
            this.items.add(items);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.items = items;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Contracts that))
            return false;
        return Objects.equals(items, that.items) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Contracts[items=%s, position=%s]".formatted(items, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(items, position);
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
