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
public final class BinaryOperator extends JavaSourceElement implements Operator {

    private final BinaryOperatorKind kind;

    private final Expression left;

    private final Expression right;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public BinaryOperatorKind kind() {
        return kind;
    }

    public Expression left() {
        return left;
    }

    public Expression right() {
        return right;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public BinaryOperator(BinaryOperatorKind kind, Expression left, Expression right, @EqEx @Nullable PositionInfo positionInfo) {
        this.kind = Objects.requireNonNull(kind);
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.positionInfo = positionInfo;
    }

    public BinaryOperator(BinaryOperatorKind kind, Expression left, Expression right) {
        this.kind = Objects.requireNonNull(kind);
        this.left = Objects.requireNonNull(left);
        this.right = Objects.requireNonNull(right);
        this.positionInfo = null;
    }

    public BinaryOperator(BinaryOperator other) {
        this(other.kind, other.left, other.right, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof BinaryOperator other))
            return null;
        cond = MatchHelper.match(kind, other.kind, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(left, other.left, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(right, other.right, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public BinaryOperator withKind(BinaryOperatorKind kind) {
        return new BinaryOperator(kind, left(), right(), positionInfo());
    }

    public BinaryOperator withLeft(Expression left) {
        return new BinaryOperator(kind(), left, right(), positionInfo());
    }

    public BinaryOperator withRight(Expression right) {
        return new BinaryOperator(kind(), left(), right, positionInfo());
    }

    public BinaryOperator withPositionInfo(PositionInfo positionInfo) {
        return new BinaryOperator(kind(), left(), right(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public BinaryOperatorKind kind;

        @Nullable()
        public Expression left;

        @Nullable()
        public Expression right;

        @Nullable()
        public PositionInfo positionInfo;

        public BinaryOperator build() {
            return new BinaryOperator(kind, left, right, positionInfo);
        }

        public Builder kind(BinaryOperatorKind kind) {
            this.kind = kind;
            return this;
        }

        public Builder left(Expression left) {
            this.left = left;
            return this;
        }

        public Builder right(Expression right) {
            this.right = right;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.kind = kind;
        b.left = left;
        b.right = right;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof BinaryOperator that))
            return false;
        return Objects.equals(kind, that.kind) && Objects.equals(left, that.left) && Objects.equals(right, that.right);
    }

    @Override()
    public String toString() {
        return "BinaryOperator[kind=%s, left=%s, right=%s, positionInfo=%s]".formatted(kind, left, right, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(kind, left, right);
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
