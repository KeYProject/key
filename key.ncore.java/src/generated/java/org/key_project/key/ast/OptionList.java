package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OptionList extends BaseAstNode {

    private List<OptionExpr> options;

    @Nullable
    private Position position;

    public List<OptionExpr> options() {
        return options;
    }

    public OptionList setOptions(List<OptionExpr> value) {
        options = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OptionList setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OptionList(List<OptionExpr> options, @Nullable Position position) {
        this.options = Objects.requireNonNull(options);
        this.position = position;
    }

    public OptionList(List<OptionExpr> options) {
        this.options = Objects.requireNonNull(options);
        this.position = null;
    }

    public OptionList(OptionList other) {
        this(other.options, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<OptionExpr> options;

        @Nullable()
        public Position position;

        public OptionList build() {
            return new OptionList(options, position);
        }

        public Builder options(List<OptionExpr> options) {
            this.options = options;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder options(OptionExpr options) {
            if (this.options == null)
                this.options = new ArrayList<>();
            this.options.add(options);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.options = options;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OptionList that))
            return false;
        return Objects.equals(options, that.options) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OptionList[options=%s, position=%s]".formatted(options, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(options, position);
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
