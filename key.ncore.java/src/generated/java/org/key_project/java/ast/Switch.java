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
public final class Switch extends JavaSourceElement implements BranchStatement {

    private final Expression expression;

    private final ImmutableList<Branch> branches;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression expression() {
        return expression;
    }

    public ImmutableList<Branch> branches() {
        return branches;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Switch(Expression expression, ImmutableList<Branch> branches, @EqEx @Nullable PositionInfo positionInfo) {
        this.expression = Objects.requireNonNull(expression);
        this.branches = Objects.requireNonNull(branches);
        this.positionInfo = positionInfo;
    }

    public Switch(Expression expression, ImmutableList<Branch> branches) {
        this.expression = Objects.requireNonNull(expression);
        this.branches = Objects.requireNonNull(branches);
        this.positionInfo = null;
    }

    public Switch(Switch other) {
        this(other.expression, other.branches, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Switch other))
            return null;
        cond = MatchHelper.match(expression, other.expression, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(branches, other.branches, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Switch withExpression(Expression expression) {
        return new Switch(expression, branches(), positionInfo());
    }

    public Switch withBranches(ImmutableList<Branch> branches) {
        return new Switch(expression(), branches, positionInfo());
    }

    public Switch withPositionInfo(PositionInfo positionInfo) {
        return new Switch(expression(), branches(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression expression;

        @Nullable()
        public ImmutableList<Branch> branches;

        @Nullable()
        public PositionInfo positionInfo;

        public Switch build() {
            return new Switch(expression, branches, positionInfo);
        }

        public Builder expression(Expression expression) {
            this.expression = expression;
            return this;
        }

        public Builder branches(ImmutableList<Branch> branches) {
            this.branches = branches;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder branches(Branch branches) {
            if (this.branches == null) {
                this.branches = ImmutableList.of(branches);
                return this;
            }
            this.branches = this.branches.append(branches);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.expression = expression;
        b.branches = branches;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Switch that))
            return false;
        return Objects.equals(expression, that.expression) && Objects.equals(branches, that.branches);
    }

    @Override()
    public String toString() {
        return "Switch[expression=%s, branches=%s, positionInfo=%s]".formatted(expression, branches, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(expression, branches);
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
