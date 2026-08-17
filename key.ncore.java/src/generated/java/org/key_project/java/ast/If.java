package org.key_project.java.ast;

import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;
import de.uka.ilkd.key.java.Services;
import java.util.*;
import org.jspecify.annotations.NullMarked;

@NullMarked()
public final class If extends JavaSourceElement implements BranchStatement {

    private final Expression condition;

    private final Statement thenBranch;

    private final Statement elseBranch;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression condition() {
        return condition;
    }

    public Statement thenBranch() {
        return thenBranch;
    }

    public Statement elseBranch() {
        return elseBranch;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public If(Expression condition, Statement thenBranch, Statement elseBranch, @EqEx @Nullable PositionInfo positionInfo) {
        this.condition = Objects.requireNonNull(condition);
        this.thenBranch = Objects.requireNonNull(thenBranch);
        this.elseBranch = Objects.requireNonNull(elseBranch);
        this.positionInfo = positionInfo;
    }

    public If(Expression condition, Statement thenBranch, Statement elseBranch) {
        this.condition = Objects.requireNonNull(condition);
        this.thenBranch = Objects.requireNonNull(thenBranch);
        this.elseBranch = Objects.requireNonNull(elseBranch);
        this.positionInfo = null;
    }

    public If(If other) {
        this(other.condition, other.thenBranch, other.elseBranch, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof If other))
            return null;
        cond = MatchHelper.match(condition, other.condition, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(thenBranch, other.thenBranch, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(elseBranch, other.elseBranch, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public If withCondition(Expression condition) {
        return new If(condition, thenBranch(), elseBranch(), positionInfo());
    }

    public If withThenBranch(Statement thenBranch) {
        return new If(condition(), thenBranch, elseBranch(), positionInfo());
    }

    public If withElseBranch(Statement elseBranch) {
        return new If(condition(), thenBranch(), elseBranch, positionInfo());
    }

    public If withPositionInfo(PositionInfo positionInfo) {
        return new If(condition(), thenBranch(), elseBranch(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression condition;

        @Nullable()
        public Statement thenBranch;

        @Nullable()
        public Statement elseBranch;

        @Nullable()
        public PositionInfo positionInfo;

        public If build() {
            return new If(condition, thenBranch, elseBranch, positionInfo);
        }

        public Builder condition(Expression condition) {
            this.condition = condition;
            return this;
        }

        public Builder thenBranch(Statement thenBranch) {
            this.thenBranch = thenBranch;
            return this;
        }

        public Builder elseBranch(Statement elseBranch) {
            this.elseBranch = elseBranch;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.condition = condition;
        b.thenBranch = thenBranch;
        b.elseBranch = elseBranch;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof If that))
            return false;
        return Objects.equals(condition, that.condition) && Objects.equals(thenBranch, that.thenBranch) && Objects.equals(elseBranch, that.elseBranch);
    }

    @Override()
    public String toString() {
        return "If[condition=%s, thenBranch=%s, elseBranch=%s, positionInfo=%s]".formatted(condition, thenBranch, elseBranch, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(condition, thenBranch, elseBranch);
        return hashCode;
    }

    public <R> R accept(org.key_project.java.ast.visitor.Visitor<R> visitor) {
        return visitor.visit(this);
    }

    public <R, A> R accept(org.key_project.java.ast.visitor.ArgVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public void accept(org.key_project.java.ast.visitor.VoidVisitor visitor) {
        visitor.visit(this);
    }
}
