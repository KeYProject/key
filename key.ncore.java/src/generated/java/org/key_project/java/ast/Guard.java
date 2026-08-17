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
public final class Guard extends JavaSourceElement implements JavaProgramElement {

    private final Expression expr;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression expr() {
        return expr;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Guard(Expression expr, @EqEx @Nullable PositionInfo positionInfo) {
        this.expr = Objects.requireNonNull(expr);
        this.positionInfo = positionInfo;
    }

    public Guard(Expression expr) {
        this.expr = Objects.requireNonNull(expr);
        this.positionInfo = null;
    }

    public Guard(Guard other) {
        this(other.expr, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Guard other))
            return null;
        cond = MatchHelper.match(expr, other.expr, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Guard withExpr(Expression expr) {
        return new Guard(expr, positionInfo());
    }

    public Guard withPositionInfo(PositionInfo positionInfo) {
        return new Guard(expr(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression expr;

        @Nullable()
        public PositionInfo positionInfo;

        public Guard build() {
            return new Guard(expr, positionInfo);
        }

        public Builder expr(Expression expr) {
            this.expr = expr;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.expr = expr;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Guard that))
            return false;
        return Objects.equals(expr, that.expr);
    }

    @Override()
    public String toString() {
        return "Guard[expr=%s, positionInfo=%s]".formatted(expr, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(expr);
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
