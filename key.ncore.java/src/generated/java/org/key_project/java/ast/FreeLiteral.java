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
public final class FreeLiteral extends JavaSourceElement implements Literal {

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final String value;

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public String value() {
        return value;
    }

    public FreeLiteral(@EqEx @Nullable PositionInfo positionInfo, String value) {
        this.positionInfo = positionInfo;
        this.value = Objects.requireNonNull(value);
    }

    public FreeLiteral(String value) {
        this.positionInfo = null;
        this.value = Objects.requireNonNull(value);
    }

    public FreeLiteral(FreeLiteral other) {
        this(other.positionInfo, other.value);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof FreeLiteral other))
            return null;
        cond = MatchHelper.match(value, other.value, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public FreeLiteral withPositionInfo(PositionInfo positionInfo) {
        return new FreeLiteral(positionInfo, value());
    }

    public FreeLiteral withValue(String value) {
        return new FreeLiteral(positionInfo(), value);
    }

    public final static class Builder {

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public String value;

        public FreeLiteral build() {
            return new FreeLiteral(positionInfo, value);
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder value(String value) {
            this.value = value;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.positionInfo = positionInfo;
        b.value = value;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FreeLiteral that))
            return false;
        return Objects.equals(value, that.value);
    }

    @Override()
    public String toString() {
        return "FreeLiteral[positionInfo=%s, value=%s]".formatted(positionInfo, value);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(value);
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
