package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Proof extends BaseAstNode {

    @Nullable
    private Position position;

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Proof setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Proof(@Nullable Position position) {
        this.position = position;
    }

    public Proof() {
        this.position = null;
    }

    public Proof(Proof other) {
        this(other.position);
    }

    public final static class Builder {

        @Nullable()
        public Position position;

        public Proof build() {
            return new Proof(position);
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Proof that))
            return false;
        return Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Proof[position=%s]".formatted(position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(position);
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
