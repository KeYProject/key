package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class GoalSpec extends BaseAstNode {

    private TermOrSeq termOrSeq;

    @Nullable
    private Position position;

    public TermOrSeq termOrSeq() {
        return termOrSeq;
    }

    public GoalSpec setTermOrSeq(TermOrSeq value) {
        termOrSeq = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public GoalSpec setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public GoalSpec(TermOrSeq termOrSeq, @Nullable Position position) {
        this.termOrSeq = Objects.requireNonNull(termOrSeq);
        this.position = position;
    }

    public GoalSpec(TermOrSeq termOrSeq) {
        this.termOrSeq = Objects.requireNonNull(termOrSeq);
        this.position = null;
    }

    public GoalSpec(GoalSpec other) {
        this(other.termOrSeq, other.position);
    }

    public final static class Builder {

        @Nullable()
        public TermOrSeq termOrSeq;

        @Nullable()
        public Position position;

        public GoalSpec build() {
            return new GoalSpec(termOrSeq, position);
        }

        public Builder termOrSeq(TermOrSeq termOrSeq) {
            this.termOrSeq = termOrSeq;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.termOrSeq = termOrSeq;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof GoalSpec that))
            return false;
        return Objects.equals(termOrSeq, that.termOrSeq) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "GoalSpec[termOrSeq=%s, position=%s]".formatted(termOrSeq, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(termOrSeq, position);
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
