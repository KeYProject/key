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
public final class Try extends JavaSourceElement implements BranchStatement {

    private final StatementBlock tryBlock;

    private final ImmutableList<Catch> catches;

    @Nullable
    private final StatementBlock finallyBlock;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public StatementBlock tryBlock() {
        return tryBlock;
    }

    public ImmutableList<Catch> catches() {
        return catches;
    }

    @Nullable()
    public StatementBlock finallyBlock() {
        return finallyBlock;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Try(StatementBlock tryBlock, ImmutableList<Catch> catches, @Nullable StatementBlock finallyBlock, @EqEx @Nullable PositionInfo positionInfo) {
        this.tryBlock = Objects.requireNonNull(tryBlock);
        this.catches = Objects.requireNonNull(catches);
        this.finallyBlock = finallyBlock;
        this.positionInfo = positionInfo;
    }

    public Try(StatementBlock tryBlock, ImmutableList<Catch> catches) {
        this.tryBlock = Objects.requireNonNull(tryBlock);
        this.catches = Objects.requireNonNull(catches);
        this.finallyBlock = null;
        this.positionInfo = null;
    }

    public Try(Try other) {
        this(other.tryBlock, other.catches, other.finallyBlock, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Try other))
            return null;
        cond = MatchHelper.match(tryBlock, other.tryBlock, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(catches, other.catches, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(finallyBlock, other.finallyBlock, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Try withTryBlock(StatementBlock tryBlock) {
        return new Try(tryBlock, catches(), finallyBlock(), positionInfo());
    }

    public Try withCatches(ImmutableList<Catch> catches) {
        return new Try(tryBlock(), catches, finallyBlock(), positionInfo());
    }

    public Try withFinallyBlock(StatementBlock finallyBlock) {
        return new Try(tryBlock(), catches(), finallyBlock, positionInfo());
    }

    public Try withPositionInfo(PositionInfo positionInfo) {
        return new Try(tryBlock(), catches(), finallyBlock(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public StatementBlock tryBlock;

        @Nullable()
        public ImmutableList<Catch> catches;

        @Nullable()
        public StatementBlock finallyBlock;

        @Nullable()
        public PositionInfo positionInfo;

        public Try build() {
            return new Try(tryBlock, catches, finallyBlock, positionInfo);
        }

        public Builder tryBlock(StatementBlock tryBlock) {
            this.tryBlock = tryBlock;
            return this;
        }

        public Builder catches(ImmutableList<Catch> catches) {
            this.catches = catches;
            return this;
        }

        public Builder finallyBlock(StatementBlock finallyBlock) {
            this.finallyBlock = finallyBlock;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder catches(Catch catches) {
            if (this.catches == null)
                this.catches = new ArrayList<>();
            this.catches.add(catches);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.tryBlock = tryBlock;
        b.catches = catches;
        b.finallyBlock = finallyBlock;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Try that))
            return false;
        return Objects.equals(tryBlock, that.tryBlock) && Objects.equals(catches, that.catches) && Objects.equals(finallyBlock, that.finallyBlock);
    }

    @Override()
    public String toString() {
        return "Try[tryBlock=%s, catches=%s, finallyBlock=%s, positionInfo=%s]".formatted(tryBlock, catches, finallyBlock, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(tryBlock, catches, finallyBlock);
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
