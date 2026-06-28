package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ProgVarDecls extends BaseAstNode {

    private List<KeyJavaType> types;

    private List<List<String>> varNames;

    @Nullable
    private Position position;

    public List<KeyJavaType> types() {
        return types;
    }

    public ProgVarDecls setTypes(List<KeyJavaType> value) {
        types = value;
        return this;
    }

    public List<List<String>> varNames() {
        return varNames;
    }

    public ProgVarDecls setVarNames(List<List<String>> value) {
        varNames = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ProgVarDecls setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ProgVarDecls(List<KeyJavaType> types, List<List<String>> varNames, @Nullable Position position) {
        this.types = Objects.requireNonNull(types);
        this.varNames = Objects.requireNonNull(varNames);
        this.position = position;
    }

    public ProgVarDecls(List<KeyJavaType> types, List<List<String>> varNames) {
        this.types = Objects.requireNonNull(types);
        this.varNames = Objects.requireNonNull(varNames);
        this.position = null;
    }

    public ProgVarDecls(ProgVarDecls other) {
        this(other.types, other.varNames, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<KeyJavaType> types;

        @Nullable()
        public List<List<String>> varNames;

        @Nullable()
        public Position position;

        public ProgVarDecls build() {
            return new ProgVarDecls(types, varNames, position);
        }

        public Builder types(List<KeyJavaType> types) {
            this.types = types;
            return this;
        }

        public Builder varNames(List<List<String>> varNames) {
            this.varNames = varNames;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder types(KeyJavaType types) {
            if (this.types == null)
                this.types = new ArrayList<>();
            this.types.add(types);
            return this;
        }

        public Builder varNames(List<String> varNames) {
            if (this.varNames == null)
                this.varNames = new ArrayList<>();
            this.varNames.add(varNames);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.types = types;
        b.varNames = varNames;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ProgVarDecls that))
            return false;
        return Objects.equals(types, that.types) && Objects.equals(varNames, that.varNames) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ProgVarDecls[types=%s, varNames=%s, position=%s]".formatted(types, varNames, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(types, varNames, position);
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
