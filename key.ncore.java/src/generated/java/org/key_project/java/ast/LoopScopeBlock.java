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
public final class LoopScopeBlock extends JavaSourceElement implements JavaStatement {

    private final Expression variant;

    private final Statement body;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression variant() {
        return variant;
    }

    public Statement body() {
        return body;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public LoopScopeBlock(Expression variant, Statement body, @EqEx @Nullable PositionInfo positionInfo) {
        this.variant = Objects.requireNonNull(variant);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public LoopScopeBlock(Expression variant, Statement body) {
        this.variant = Objects.requireNonNull(variant);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public LoopScopeBlock(LoopScopeBlock other) {
        this(other.variant, other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof LoopScopeBlock other))
            return null;
        cond = MatchHelper.match(variant, other.variant, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public LoopScopeBlock withVariant(Expression variant) {
        return new LoopScopeBlock(variant, body(), positionInfo());
    }

    public LoopScopeBlock withBody(Statement body) {
        return new LoopScopeBlock(variant(), body, positionInfo());
    }

    public LoopScopeBlock withPositionInfo(PositionInfo positionInfo) {
        return new LoopScopeBlock(variant(), body(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression variant;

        @Nullable()
        public Statement body;

        @Nullable()
        public PositionInfo positionInfo;

        public LoopScopeBlock build() {
            return new LoopScopeBlock(variant, body, positionInfo);
        }

        public Builder variant(Expression variant) {
            this.variant = variant;
            return this;
        }

        public Builder body(Statement body) {
            this.body = body;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.variant = variant;
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof LoopScopeBlock that))
            return false;
        return Objects.equals(variant, that.variant) && Objects.equals(body, that.body);
    }

    @Override()
    public String toString() {
        return "LoopScopeBlock[variant=%s, body=%s, positionInfo=%s]".formatted(variant, body, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(variant, body);
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
