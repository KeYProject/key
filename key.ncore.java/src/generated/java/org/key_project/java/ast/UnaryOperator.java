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
public final class UnaryOperator extends JavaSourceElement {

    private final UnaryOperatorKind kind;

    private final Expression child;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public UnaryOperatorKind kind() {
        return kind;
    }

    public Expression child() {
        return child;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public UnaryOperator(UnaryOperatorKind kind, Expression child, @EqEx @Nullable PositionInfo positionInfo) {
        this.kind = Objects.requireNonNull(kind);
        this.child = Objects.requireNonNull(child);
        this.positionInfo = positionInfo;
    }

    public UnaryOperator(UnaryOperatorKind kind, Expression child) {
        this.kind = Objects.requireNonNull(kind);
        this.child = Objects.requireNonNull(child);
        this.positionInfo = null;
    }

    public UnaryOperator(UnaryOperator other) {
        this(other.kind, other.child, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof UnaryOperator other))
            return null;
        cond = MatchHelper.match(kind, other.kind, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(child, other.child, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public UnaryOperator withKind(UnaryOperatorKind kind) {
        return new UnaryOperator(kind, child(), positionInfo());
    }

    public UnaryOperator withChild(Expression child) {
        return new UnaryOperator(kind(), child, positionInfo());
    }

    public UnaryOperator withPositionInfo(PositionInfo positionInfo) {
        return new UnaryOperator(kind(), child(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public UnaryOperatorKind kind;

        @Nullable()
        public Expression child;

        @Nullable()
        public PositionInfo positionInfo;

        public UnaryOperator build() {
            return new UnaryOperator(kind, child, positionInfo);
        }

        public Builder kind(UnaryOperatorKind kind) {
            this.kind = kind;
            return this;
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
        b.kind = kind;
        b.child = child;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof UnaryOperator that))
            return false;
        return Objects.equals(kind, that.kind) && Objects.equals(child, that.child);
    }

    @Override()
    public String toString() {
        return "UnaryOperator[kind=%s, child=%s, positionInfo=%s]".formatted(kind, child, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(kind, child);
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
