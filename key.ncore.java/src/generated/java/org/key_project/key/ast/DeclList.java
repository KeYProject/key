package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class DeclList extends BaseAstNode {

    private List<Declaration> declarations;

    @Nullable
    private Position position;

    public List<Declaration> declarations() {
        return declarations;
    }

    public DeclList setDeclarations(List<Declaration> value) {
        declarations = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public DeclList setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public DeclList(List<Declaration> declarations, @Nullable Position position) {
        this.declarations = Objects.requireNonNull(declarations);
        this.position = position;
    }

    public DeclList(List<Declaration> declarations) {
        this.declarations = Objects.requireNonNull(declarations);
        this.position = null;
    }

    public DeclList(DeclList other) {
        this(other.declarations, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<Declaration> declarations;

        @Nullable()
        public Position position;

        public DeclList build() {
            return new DeclList(declarations, position);
        }

        public Builder declarations(List<Declaration> declarations) {
            this.declarations = declarations;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder declarations(Declaration declarations) {
            if (this.declarations == null)
                this.declarations = new ArrayList<>();
            this.declarations.add(declarations);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.declarations = declarations;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof DeclList that))
            return false;
        return Objects.equals(declarations, that.declarations) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "DeclList[declarations=%s, position=%s]".formatted(declarations, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(declarations, position);
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
