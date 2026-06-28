package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class IfThenElseTerm extends BaseAstNode {

    private Term condition;

    private Term thenBranch;

    private Term elseBranch;

    @Nullable
    private Position position;

    public Term condition() {
        return condition;
    }

    public IfThenElseTerm setCondition(Term value) {
        condition = value;
        return this;
    }

    public Term thenBranch() {
        return thenBranch;
    }

    public IfThenElseTerm setThenBranch(Term value) {
        thenBranch = value;
        return this;
    }

    public Term elseBranch() {
        return elseBranch;
    }

    public IfThenElseTerm setElseBranch(Term value) {
        elseBranch = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public IfThenElseTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public IfThenElseTerm(Term condition, Term thenBranch, Term elseBranch, @Nullable Position position) {
        this.condition = Objects.requireNonNull(condition);
        this.thenBranch = Objects.requireNonNull(thenBranch);
        this.elseBranch = Objects.requireNonNull(elseBranch);
        this.position = position;
    }

    public IfThenElseTerm(Term condition, Term thenBranch, Term elseBranch) {
        this.condition = Objects.requireNonNull(condition);
        this.thenBranch = Objects.requireNonNull(thenBranch);
        this.elseBranch = Objects.requireNonNull(elseBranch);
        this.position = null;
    }

    public IfThenElseTerm(IfThenElseTerm other) {
        this(other.condition, other.thenBranch, other.elseBranch, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term condition;

        @Nullable()
        public Term thenBranch;

        @Nullable()
        public Term elseBranch;

        @Nullable()
        public Position position;

        public IfThenElseTerm build() {
            return new IfThenElseTerm(condition, thenBranch, elseBranch, position);
        }

        public Builder condition(Term condition) {
            this.condition = condition;
            return this;
        }

        public Builder thenBranch(Term thenBranch) {
            this.thenBranch = thenBranch;
            return this;
        }

        public Builder elseBranch(Term elseBranch) {
            this.elseBranch = elseBranch;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.condition = condition;
        b.thenBranch = thenBranch;
        b.elseBranch = elseBranch;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof IfThenElseTerm that))
            return false;
        return Objects.equals(condition, that.condition) && Objects.equals(thenBranch, that.thenBranch) && Objects.equals(elseBranch, that.elseBranch) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "IfThenElseTerm[condition=%s, thenBranch=%s, elseBranch=%s, position=%s]".formatted(condition, thenBranch, elseBranch, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(condition, thenBranch, elseBranch, position);
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
