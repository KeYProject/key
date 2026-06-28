package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class CKey extends BaseAstNode {

    private String key;

    @Nullable
    private Position position;

    public String key() {
        return key;
    }

    public CKey setKey(String value) {
        key = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public CKey setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public CKey(String key, @Nullable Position position) {
        this.key = Objects.requireNonNull(key);
        this.position = position;
    }

    public CKey(String key) {
        this.key = Objects.requireNonNull(key);
        this.position = null;
    }

    public CKey(CKey other) {
        this(other.key, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String key;

        @Nullable()
        public Position position;

        public CKey build() {
            return new CKey(key, position);
        }

        public Builder key(String key) {
            this.key = key;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.key = key;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof CKey that))
            return false;
        return Objects.equals(key, that.key) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "CKey[key=%s, position=%s]".formatted(key, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(key, position);
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
