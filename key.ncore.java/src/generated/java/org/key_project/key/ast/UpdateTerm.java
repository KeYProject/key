package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class UpdateTerm extends BaseAstNode {

    private java.util.List<ElementaryUpdateTerm> updates;

    @Nullable
    private Position position;

    public java.util.List<ElementaryUpdateTerm> updates() {
        return updates;
    }

    public UpdateTerm setUpdates(java.util.List<ElementaryUpdateTerm> value) {
        updates = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public UpdateTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public UpdateTerm(java.util.List<ElementaryUpdateTerm> updates, @Nullable Position position) {
        this.updates = Objects.requireNonNull(updates);
        this.position = position;
    }

    public UpdateTerm(java.util.List<ElementaryUpdateTerm> updates) {
        this.updates = Objects.requireNonNull(updates);
        this.position = null;
    }

    public UpdateTerm(UpdateTerm other) {
        this(other.updates, other.position);
    }

    public final static class Builder {

        @Nullable()
        public java.util.List<ElementaryUpdateTerm> updates;

        @Nullable()
        public Position position;

        public UpdateTerm build() {
            return new UpdateTerm(updates, position);
        }

        public Builder updates(java.util.List<ElementaryUpdateTerm> updates) {
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
        if (!(o instanceof UpdateTerm that))
            return false;
        return Objects.equals(updates, that.updates) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "UpdateTerm[updates=%s, position=%s]".formatted(updates, position);
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
