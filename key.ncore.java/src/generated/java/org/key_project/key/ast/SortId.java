package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class SortId extends BaseAstNode {

    private List<String> parts;

    @Nullable
    private FormalSortArgs formalArgs;

    private int arrayDimensions;

    @Nullable
    private Position position;

    public List<String> parts() {
        return parts;
    }

    public SortId setParts(List<String> value) {
        parts = value;
        return this;
    }

    @Nullable()
    public FormalSortArgs formalArgs() {
        return formalArgs;
    }

    public SortId setFormalArgs(@Nullable() FormalSortArgs value) {
        formalArgs = value;
        return this;
    }

    public int arrayDimensions() {
        return arrayDimensions;
    }

    public SortId setArrayDimensions(int value) {
        arrayDimensions = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public SortId setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public SortId(List<String> parts, @Nullable FormalSortArgs formalArgs, int arrayDimensions, @Nullable Position position) {
        this.parts = Objects.requireNonNull(parts);
        this.formalArgs = formalArgs;
        this.arrayDimensions = Objects.requireNonNull(arrayDimensions);
        this.position = position;
    }

    public SortId(List<String> parts, int arrayDimensions) {
        this.parts = Objects.requireNonNull(parts);
        this.formalArgs = null;
        this.arrayDimensions = Objects.requireNonNull(arrayDimensions);
        this.position = null;
    }

    public SortId(SortId other) {
        this(other.parts, other.formalArgs, other.arrayDimensions, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<String> parts;

        @Nullable()
        public FormalSortArgs formalArgs;

        @Nullable()
        public int arrayDimensions;

        @Nullable()
        public Position position;

        public SortId build() {
            return new SortId(parts, formalArgs, arrayDimensions, position);
        }

        public Builder parts(List<String> parts) {
            this.parts = parts;
            return this;
        }

        public Builder formalArgs(FormalSortArgs formalArgs) {
            this.formalArgs = formalArgs;
            return this;
        }

        public Builder arrayDimensions(int arrayDimensions) {
            this.arrayDimensions = arrayDimensions;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder parts(String parts) {
            if (this.parts == null)
                this.parts = new ArrayList<>();
            this.parts.add(parts);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.parts = parts;
        b.formalArgs = formalArgs;
        b.arrayDimensions = arrayDimensions;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SortId that))
            return false;
        return Objects.equals(parts, that.parts) && Objects.equals(formalArgs, that.formalArgs) && Objects.equals(arrayDimensions, that.arrayDimensions) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "SortId[parts=%s, formalArgs=%s, arrayDimensions=%s, position=%s]".formatted(parts, formalArgs, arrayDimensions, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(parts, formalArgs, arrayDimensions, position);
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
