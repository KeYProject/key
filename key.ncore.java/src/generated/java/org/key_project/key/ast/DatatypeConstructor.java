package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class DatatypeConstructor extends BaseAstNode {

    private SimpleIdentDots name;

    private ArgSorts argSorts;

    @Nullable
    private Position position;

    public SimpleIdentDots name() {
        return name;
    }

    public DatatypeConstructor setName(SimpleIdentDots value) {
        name = value;
        return this;
    }

    public ArgSorts argSorts() {
        return argSorts;
    }

    public DatatypeConstructor setArgSorts(ArgSorts value) {
        argSorts = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public DatatypeConstructor setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public DatatypeConstructor(SimpleIdentDots name, ArgSorts argSorts, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.argSorts = Objects.requireNonNull(argSorts);
        this.position = position;
    }

    public DatatypeConstructor(SimpleIdentDots name, ArgSorts argSorts) {
        this.name = Objects.requireNonNull(name);
        this.argSorts = Objects.requireNonNull(argSorts);
        this.position = null;
    }

    public DatatypeConstructor(DatatypeConstructor other) {
        this(other.name, other.argSorts, other.position);
    }

    public final static class Builder {

        @Nullable()
        public SimpleIdentDots name;

        @Nullable()
        public ArgSorts argSorts;

        @Nullable()
        public Position position;

        public DatatypeConstructor build() {
            return new DatatypeConstructor(name, argSorts, position);
        }

        public Builder name(SimpleIdentDots name) {
            this.name = name;
            return this;
        }

        public Builder argSorts(ArgSorts argSorts) {
            this.argSorts = argSorts;
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
        b.argSorts = argSorts;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof DatatypeConstructor that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(argSorts, that.argSorts) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "DatatypeConstructor[name=%s, argSorts=%s, position=%s]".formatted(name, argSorts, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, argSorts, position);
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
