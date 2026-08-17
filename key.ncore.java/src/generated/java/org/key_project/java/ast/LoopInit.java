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
public final class LoopInit extends JavaSourceElement implements JavaProgramElement {

    private final ImmutableList<LoopInitializer> inits;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ImmutableList<LoopInitializer> inits() {
        return inits;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public LoopInit(ImmutableList<LoopInitializer> inits, @EqEx @Nullable PositionInfo positionInfo) {
        this.inits = Objects.requireNonNull(inits);
        this.positionInfo = positionInfo;
    }

    public LoopInit(ImmutableList<LoopInitializer> inits) {
        this.inits = Objects.requireNonNull(inits);
        this.positionInfo = null;
    }

    public LoopInit(LoopInit other) {
        this(other.inits, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof LoopInit other))
            return null;
        cond = MatchHelper.match(inits, other.inits, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public LoopInit withInits(ImmutableList<LoopInitializer> inits) {
        return new LoopInit(inits, positionInfo());
    }

    public LoopInit withPositionInfo(PositionInfo positionInfo) {
        return new LoopInit(inits(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<LoopInitializer> inits;

        @Nullable()
        public PositionInfo positionInfo;

        public LoopInit build() {
            return new LoopInit(inits, positionInfo);
        }

        public Builder inits(ImmutableList<LoopInitializer> inits) {
            this.inits = inits;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder inits(LoopInitializer inits) {
            if (this.inits == null)
                this.inits = new ArrayList<>();
            this.inits.add(inits);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.inits = inits;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof LoopInit that))
            return false;
        return Objects.equals(inits, that.inits);
    }

    @Override()
    public String toString() {
        return "LoopInit[inits=%s, positionInfo=%s]".formatted(inits, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(inits);
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
