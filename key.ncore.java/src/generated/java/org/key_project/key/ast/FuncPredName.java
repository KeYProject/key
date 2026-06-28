package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class FuncPredName extends BaseAstNode {

    @Nullable
    private SortId sortPrefix;

    @Nullable
    private SimpleIdentDots name;

    @Nullable
    private String intLiteral;

    @Nullable
    private Position position;

    @Nullable()
    public SortId sortPrefix() {
        return sortPrefix;
    }

    public FuncPredName setSortPrefix(@Nullable() SortId value) {
        sortPrefix = value;
        return this;
    }

    @Nullable()
    public SimpleIdentDots name() {
        return name;
    }

    public FuncPredName setName(@Nullable() SimpleIdentDots value) {
        name = value;
        return this;
    }

    @Nullable()
    public String intLiteral() {
        return intLiteral;
    }

    public FuncPredName setIntLiteral(@Nullable() String value) {
        intLiteral = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public FuncPredName setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public FuncPredName(@Nullable SortId sortPrefix, @Nullable SimpleIdentDots name, @Nullable String intLiteral, @Nullable Position position) {
        this.sortPrefix = sortPrefix;
        this.name = name;
        this.intLiteral = intLiteral;
        this.position = position;
    }

    public FuncPredName() {
        this.sortPrefix = null;
        this.name = null;
        this.intLiteral = null;
        this.position = null;
    }

    public FuncPredName(FuncPredName other) {
        this(other.sortPrefix, other.name, other.intLiteral, other.position);
    }

    public final static class Builder {

        @Nullable()
        public SortId sortPrefix;

        @Nullable()
        public SimpleIdentDots name;

        @Nullable()
        public String intLiteral;

        @Nullable()
        public Position position;

        public FuncPredName build() {
            return new FuncPredName(sortPrefix, name, intLiteral, position);
        }

        public Builder sortPrefix(SortId sortPrefix) {
            this.sortPrefix = sortPrefix;
            return this;
        }

        public Builder name(SimpleIdentDots name) {
            this.name = name;
            return this;
        }

        public Builder intLiteral(String intLiteral) {
            this.intLiteral = intLiteral;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.sortPrefix = sortPrefix;
        b.name = name;
        b.intLiteral = intLiteral;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FuncPredName that))
            return false;
        return Objects.equals(sortPrefix, that.sortPrefix) && Objects.equals(name, that.name) && Objects.equals(intLiteral, that.intLiteral) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "FuncPredName[sortPrefix=%s, name=%s, intLiteral=%s, position=%s]".formatted(sortPrefix, name, intLiteral, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(sortPrefix, name, intLiteral, position);
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
