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
public final class ProgramElementName extends JavaSourceElement implements Name {

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ProgramElementName(@EqEx @Nullable PositionInfo positionInfo) {
        this.positionInfo = positionInfo;
    }

    public ProgramElementName() {
        this.positionInfo = null;
    }

    public ProgramElementName(ProgramElementName other) {
        this(other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ProgramElementName other))
            return null;
        return cond;
    }

    public ProgramElementName withPositionInfo(PositionInfo positionInfo) {
        return new ProgramElementName(positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public PositionInfo positionInfo;

        public ProgramElementName build() {
            return new ProgramElementName(positionInfo);
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
        if (!(o instanceof ProgramElementName that))
            return false;
        return true;
    }

    @Override()
    public String toString() {
        return "ProgramElementName[positionInfo=%s]".formatted(positionInfo);
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
