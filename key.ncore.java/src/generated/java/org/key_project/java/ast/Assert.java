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
public final class Assert extends JavaSourceElement implements JavaStatement {

    private final Expression expression;

    @Nullable
    private final String message;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression expression() {
        return expression;
    }

    @Nullable()
    public String message() {
        return message;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Assert(Expression expression, @Nullable String message, @EqEx @Nullable PositionInfo positionInfo) {
        this.expression = Objects.requireNonNull(expression);
        this.message = message;
        this.positionInfo = positionInfo;
    }

    public Assert(Expression expression) {
        this.expression = Objects.requireNonNull(expression);
        this.message = null;
        this.positionInfo = null;
    }

    public Assert(Assert other) {
        this(other.expression, other.message, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Assert other))
            return null;
        cond = MatchHelper.match(expression, other.expression, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(message, other.message, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Assert withExpression(Expression expression) {
        return new Assert(expression, message(), positionInfo());
    }

    public Assert withMessage(String message) {
        return new Assert(expression(), message, positionInfo());
    }

    public Assert withPositionInfo(PositionInfo positionInfo) {
        return new Assert(expression(), message(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression expression;

        @Nullable()
        public String message;

        @Nullable()
        public PositionInfo positionInfo;

        public Assert build() {
            return new Assert(expression, message, positionInfo);
        }

        public Builder expression(Expression expression) {
            this.expression = expression;
            return this;
        }

        public Builder message(String message) {
            this.message = message;
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
        b.message = message;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Assert that))
            return false;
        return Objects.equals(expression, that.expression) && Objects.equals(message, that.message);
    }

    @Override()
    public String toString() {
        return "Assert[expression=%s, message=%s, positionInfo=%s]".formatted(expression, message, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(expression, message);
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
