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
public final class MergePointStatement extends JavaSourceElement implements JavaStatement {

    private final IProgramVariable identifier;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public IProgramVariable identifier() {
        return identifier;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public MergePointStatement(IProgramVariable identifier, @EqEx @Nullable PositionInfo positionInfo) {
        this.identifier = Objects.requireNonNull(identifier);
        this.positionInfo = positionInfo;
    }

    public MergePointStatement(IProgramVariable identifier) {
        this.identifier = Objects.requireNonNull(identifier);
        this.positionInfo = null;
    }

    public MergePointStatement(MergePointStatement other) {
        this(other.identifier, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof MergePointStatement other))
            return null;
        cond = MatchHelper.match(identifier, other.identifier, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public MergePointStatement withIdentifier(IProgramVariable identifier) {
        return new MergePointStatement(identifier, positionInfo());
    }

    public MergePointStatement withPositionInfo(PositionInfo positionInfo) {
        return new MergePointStatement(identifier(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public IProgramVariable identifier;

        @Nullable()
        public PositionInfo positionInfo;

        public MergePointStatement build() {
            return new MergePointStatement(identifier, positionInfo);
        }

        public Builder identifier(IProgramVariable identifier) {
            this.identifier = identifier;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.identifier = identifier;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof MergePointStatement that))
            return false;
        return Objects.equals(identifier, that.identifier);
    }

    @Override()
    public String toString() {
        return "MergePointStatement[identifier=%s, positionInfo=%s]".formatted(identifier, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(identifier);
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
