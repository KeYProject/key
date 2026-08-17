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
public final class Conditional extends JavaSourceElement implements Operator {

    private final Expression condition;

    private final Expression thenExpr;

    private final Expression elseExpr;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression condition() {
        return condition;
    }

    public Expression thenExpr() {
        return thenExpr;
    }

    public Expression elseExpr() {
        return elseExpr;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Conditional(Expression condition, Expression thenExpr, Expression elseExpr, @EqEx @Nullable PositionInfo positionInfo) {
        this.condition = Objects.requireNonNull(condition);
        this.thenExpr = Objects.requireNonNull(thenExpr);
        this.elseExpr = Objects.requireNonNull(elseExpr);
        this.positionInfo = positionInfo;
    }

    public Conditional(Expression condition, Expression thenExpr, Expression elseExpr) {
        this.condition = Objects.requireNonNull(condition);
        this.thenExpr = Objects.requireNonNull(thenExpr);
        this.elseExpr = Objects.requireNonNull(elseExpr);
        this.positionInfo = null;
    }

    public Conditional(Conditional other) {
        this(other.condition, other.thenExpr, other.elseExpr, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Conditional other))
            return null;
        cond = MatchHelper.match(condition, other.condition, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(thenExpr, other.thenExpr, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(elseExpr, other.elseExpr, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Conditional withCondition(Expression condition) {
        return new Conditional(condition, thenExpr(), elseExpr(), positionInfo());
    }

    public Conditional withThenExpr(Expression thenExpr) {
        return new Conditional(condition(), thenExpr, elseExpr(), positionInfo());
    }

    public Conditional withElseExpr(Expression elseExpr) {
        return new Conditional(condition(), thenExpr(), elseExpr, positionInfo());
    }

    public Conditional withPositionInfo(PositionInfo positionInfo) {
        return new Conditional(condition(), thenExpr(), elseExpr(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression condition;

        @Nullable()
        public Expression thenExpr;

        @Nullable()
        public Expression elseExpr;

        @Nullable()
        public PositionInfo positionInfo;

        public Conditional build() {
            return new Conditional(condition, thenExpr, elseExpr, positionInfo);
        }

        public Builder condition(Expression condition) {
            this.condition = condition;
            return this;
        }

        public Builder thenExpr(Expression thenExpr) {
            this.thenExpr = thenExpr;
            return this;
        }

        public Builder elseExpr(Expression elseExpr) {
            this.elseExpr = elseExpr;
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
        b.thenExpr = thenExpr;
        b.elseExpr = elseExpr;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Conditional that))
            return false;
        return Objects.equals(condition, that.condition) && Objects.equals(thenExpr, that.thenExpr) && Objects.equals(elseExpr, that.elseExpr);
    }

    @Override()
    public String toString() {
        return "Conditional[condition=%s, thenExpr=%s, elseExpr=%s, positionInfo=%s]".formatted(condition, thenExpr, elseExpr, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(condition, thenExpr, elseExpr);
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
