package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ParallelTerm extends BaseAstNode {

    private List<ElementaryUpdateTerm> updates;

    @Nullable
    private Position position;

    public List<ElementaryUpdateTerm> updates() {
        return updates;
    }

    public ParallelTerm setUpdates(List<ElementaryUpdateTerm> value) {
        updates = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ParallelTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ParallelTerm(List<ElementaryUpdateTerm> updates, @Nullable Position position) {
        this.updates = Objects.requireNonNull(updates);
        this.position = position;
    }

    public ParallelTerm(List<ElementaryUpdateTerm> updates) {
        this.updates = Objects.requireNonNull(updates);
        this.position = null;
    }

    public ParallelTerm(ParallelTerm other) {
        this(other.updates, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<ElementaryUpdateTerm> updates;

        @Nullable()
        public Position position;

        public ParallelTerm build() {
            return new ParallelTerm(updates, position);
        }

        public Builder updates(List<ElementaryUpdateTerm> updates) {
            this.updates = updates;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder updates(ElementaryUpdateTerm updates) {
            if (this.updates == null)
                this.updates = new ArrayList<>();
            this.updates.add(updates);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.updates = updates;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ParallelTerm that))
            return false;
        return Objects.equals(updates, that.updates) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ParallelTerm[updates=%s, position=%s]".formatted(updates, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(updates, position);
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
