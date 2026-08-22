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
public final class Throw extends JavaSourceElement implements ExpressionJumpStatement {

    private final Expression expression;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @java.lang.Override()
    public Expression expression() {
        return expression;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Throw(Expression expression, @EqEx @Nullable PositionInfo positionInfo) {
        this.expression = Objects.requireNonNull(expression);
        this.positionInfo = positionInfo;
    }

    public Throw(Expression expression) {
        this.expression = Objects.requireNonNull(expression);
        this.positionInfo = null;
    }

    public Throw(Throw other) {
        this(other.expression, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Throw other))
            return null;
        cond = MatchHelper.match(expression, other.expression, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Throw withExpression(Expression expression) {
        return new Throw(expression, positionInfo());
    }

    public Throw withPositionInfo(PositionInfo positionInfo) {
        return new Throw(expression(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression expression;

        @Nullable()
        public PositionInfo positionInfo;

        public Throw build() {
            return new Throw(expression, positionInfo);
        }

        public Builder expression(Expression expression) {
            this.expression = expression;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.expression = expression;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Throw that))
            return false;
        return Objects.equals(expression, that.expression);
    }

    @Override()
    public String toString() {
        return "Throw[expression=%s, positionInfo=%s]".formatted(expression, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(expression);
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
