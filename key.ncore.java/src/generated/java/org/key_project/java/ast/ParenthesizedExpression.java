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
public final class ParenthesizedExpression extends JavaSourceElement implements Expression {

    private final Expression child;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression child() {
        return child;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ParenthesizedExpression(Expression child, @EqEx @Nullable PositionInfo positionInfo) {
        this.child = Objects.requireNonNull(child);
        this.positionInfo = positionInfo;
    }

    public ParenthesizedExpression(Expression child) {
        this.child = Objects.requireNonNull(child);
        this.positionInfo = null;
    }

    public ParenthesizedExpression(ParenthesizedExpression other) {
        this(other.child, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ParenthesizedExpression other))
            return null;
        cond = MatchHelper.match(child, other.child, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ParenthesizedExpression withChild(Expression child) {
        return new ParenthesizedExpression(child, positionInfo());
    }

    public ParenthesizedExpression withPositionInfo(PositionInfo positionInfo) {
        return new ParenthesizedExpression(child(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression child;

        @Nullable()
        public PositionInfo positionInfo;

        public ParenthesizedExpression build() {
            return new ParenthesizedExpression(child, positionInfo);
        }

        public Builder child(Expression child) {
            this.child = child;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.child = child;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ParenthesizedExpression that))
            return false;
        return Objects.equals(child, that.child);
    }

    @Override()
    public String toString() {
        return "ParenthesizedExpression[child=%s, positionInfo=%s]".formatted(child, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(child);
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
