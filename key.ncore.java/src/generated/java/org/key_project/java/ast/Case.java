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
public final class Case extends JavaSourceElement {

    private final Expression expression;

    private final ImmutableList<Statement> body;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression expression() {
        return expression;
    }

    public ImmutableList<Statement> body() {
        return body;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Case(Expression expression, ImmutableList<Statement> body, @EqEx @Nullable PositionInfo positionInfo) {
        this.expression = Objects.requireNonNull(expression);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public Case(Expression expression, ImmutableList<Statement> body) {
        this.expression = Objects.requireNonNull(expression);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public Case(Case other) {
        this(other.expression, other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Case other))
            return null;
        cond = MatchHelper.match(expression, other.expression, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Case withExpression(Expression expression) {
        return new Case(expression, body(), positionInfo());
    }

    public Case withBody(ImmutableList<Statement> body) {
        return new Case(expression(), body, positionInfo());
    }

    public Case withPositionInfo(PositionInfo positionInfo) {
        return new Case(expression(), body(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression expression;

        @Nullable()
        public ImmutableList<Statement> body;

        @Nullable()
        public PositionInfo positionInfo;

        public Case build() {
            return new Case(expression, body, positionInfo);
        }

        public Builder expression(Expression expression) {
            this.expression = expression;
            return this;
        }

        public Builder body(ImmutableList<Statement> body) {
            this.body = body;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder body(Statement body) {
            if (this.body == null) {
                this.body = ImmutableList.of(body);
                return this;
            }
            this.body = this.body.append(body);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.expression = expression;
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Case that))
            return false;
        return Objects.equals(expression, that.expression) && Objects.equals(body, that.body);
    }

    @Override()
    public String toString() {
        return "Case[expression=%s, body=%s, positionInfo=%s]".formatted(expression, body, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(expression, body);
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
