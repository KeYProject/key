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
public final class PermIndProgramElementName extends JavaSourceElement implements IndProgramElementName {

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public PermIndProgramElementName(@EqEx @Nullable PositionInfo positionInfo) {
        this.positionInfo = positionInfo;
    }

    public PermIndProgramElementName() {
        this.positionInfo = null;
    }

    public PermIndProgramElementName(PermIndProgramElementName other) {
        this(other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof PermIndProgramElementName other))
            return null;
        return cond;
    }

    public PermIndProgramElementName withPositionInfo(PositionInfo positionInfo) {
        return new PermIndProgramElementName(positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public PositionInfo positionInfo;

        public PermIndProgramElementName build() {
            return new PermIndProgramElementName(positionInfo);
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof PermIndProgramElementName that))
            return false;
        return true;
    }

    @Override()
    public String toString() {
        return "PermIndProgramElementName[positionInfo=%s]".formatted(positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
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
