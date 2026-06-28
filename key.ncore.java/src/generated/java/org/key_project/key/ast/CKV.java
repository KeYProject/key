package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class CKV extends BaseAstNode {

    private CKey key;

    private CValue value;

    @Nullable
    private Position position;

    public CKey key() {
        return key;
    }

    public CKV setKey(CKey value) {
        key = value;
        return this;
    }

    public CValue value() {
        return value;
    }

    public CKV setValue(CValue value) {
        value = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public CKV setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public CKV(CKey key, CValue value, @Nullable Position position) {
        this.key = Objects.requireNonNull(key);
        this.value = Objects.requireNonNull(value);
        this.position = position;
    }

    public CKV(CKey key, CValue value) {
        this.key = Objects.requireNonNull(key);
        this.value = Objects.requireNonNull(value);
        this.position = null;
    }

    public CKV(CKV other) {
        this(other.key, other.value, other.position);
    }

    public final static class Builder {

        @Nullable()
        public CKey key;

        @Nullable()
        public CValue value;

        @Nullable()
        public Position position;

        public CKV build() {
            return new CKV(key, value, position);
        }

        public Builder key(CKey key) {
            this.key = key;
            return this;
        }

        public Builder value(CValue value) {
            this.value = value;
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
        b.value = value;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof CKV that))
            return false;
        return Objects.equals(key, that.key) && Objects.equals(value, that.value) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "CKV[key=%s, value=%s, position=%s]".formatted(key, value, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(key, value, position);
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
