package org.key_project.java.ast;

import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import java.util.*;
import org.jspecify.annotations.NullMarked;

@NullMarked()
public final class CcatchNonstandardParameterDeclaration extends JavaSourceElement implements JavaProgramElement {

    private final ParameterDeclaration delegate;

    private final boolean isWildcard;

    private final boolean isBreak;

    private final boolean isContinue;

    private final boolean isReturn;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ParameterDeclaration delegate() {
        return delegate;
    }

    public boolean isWildcard() {
        return isWildcard;
    }

    public boolean isBreak() {
        return isBreak;
    }

    public boolean isContinue() {
        return isContinue;
    }

    public boolean isReturn() {
        return isReturn;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public CcatchNonstandardParameterDeclaration(ParameterDeclaration delegate, boolean isWildcard, boolean isBreak, boolean isContinue, boolean isReturn, @EqEx @Nullable PositionInfo positionInfo) {
        this.delegate = Objects.requireNonNull(delegate);
        this.isWildcard = Objects.requireNonNull(isWildcard);
        this.isBreak = Objects.requireNonNull(isBreak);
        this.isContinue = Objects.requireNonNull(isContinue);
        this.isReturn = Objects.requireNonNull(isReturn);
        this.positionInfo = positionInfo;
    }

    public CcatchNonstandardParameterDeclaration(ParameterDeclaration delegate, boolean isWildcard, boolean isBreak, boolean isContinue, boolean isReturn) {
        this.delegate = Objects.requireNonNull(delegate);
        this.isWildcard = Objects.requireNonNull(isWildcard);
        this.isBreak = Objects.requireNonNull(isBreak);
        this.isContinue = Objects.requireNonNull(isContinue);
        this.isReturn = Objects.requireNonNull(isReturn);
        this.positionInfo = null;
    }

    public CcatchNonstandardParameterDeclaration(CcatchNonstandardParameterDeclaration other) {
        this(other.delegate, other.isWildcard, other.isBreak, other.isContinue, other.isReturn, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof CcatchNonstandardParameterDeclaration other))
            return null;
        cond = MatchHelper.match(delegate, other.delegate, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isWildcard, other.isWildcard, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isBreak, other.isBreak, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isContinue, other.isContinue, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isReturn, other.isReturn, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public CcatchNonstandardParameterDeclaration withDelegate(ParameterDeclaration delegate) {
        return new CcatchNonstandardParameterDeclaration(delegate, isWildcard(), isBreak(), isContinue(), isReturn(), positionInfo());
    }

    public CcatchNonstandardParameterDeclaration withIsWildcard(boolean isWildcard) {
        return new CcatchNonstandardParameterDeclaration(delegate(), isWildcard, isBreak(), isContinue(), isReturn(), positionInfo());
    }

    public CcatchNonstandardParameterDeclaration withIsBreak(boolean isBreak) {
        return new CcatchNonstandardParameterDeclaration(delegate(), isWildcard(), isBreak, isContinue(), isReturn(), positionInfo());
    }

    public CcatchNonstandardParameterDeclaration withIsContinue(boolean isContinue) {
        return new CcatchNonstandardParameterDeclaration(delegate(), isWildcard(), isBreak(), isContinue, isReturn(), positionInfo());
    }

    public CcatchNonstandardParameterDeclaration withIsReturn(boolean isReturn) {
        return new CcatchNonstandardParameterDeclaration(delegate(), isWildcard(), isBreak(), isContinue(), isReturn, positionInfo());
    }

    public CcatchNonstandardParameterDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new CcatchNonstandardParameterDeclaration(delegate(), isWildcard(), isBreak(), isContinue(), isReturn(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ParameterDeclaration delegate;

        @Nullable()
        public boolean isWildcard;

        @Nullable()
        public boolean isBreak;

        @Nullable()
        public boolean isContinue;

        @Nullable()
        public boolean isReturn;

        @Nullable()
        public PositionInfo positionInfo;

        public CcatchNonstandardParameterDeclaration build() {
            return new CcatchNonstandardParameterDeclaration(delegate, isWildcard, isBreak, isContinue, isReturn, positionInfo);
        }

        public Builder delegate(ParameterDeclaration delegate) {
            this.delegate = delegate;
            return this;
        }

        public Builder isWildcard(boolean isWildcard) {
            this.isWildcard = isWildcard;
            return this;
        }

        public Builder isBreak(boolean isBreak) {
            this.isBreak = isBreak;
            return this;
        }

        public Builder isContinue(boolean isContinue) {
            this.isContinue = isContinue;
            return this;
        }

        public Builder isReturn(boolean isReturn) {
            this.isReturn = isReturn;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.delegate = delegate;
        b.isWildcard = isWildcard;
        b.isBreak = isBreak;
        b.isContinue = isContinue;
        b.isReturn = isReturn;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof CcatchNonstandardParameterDeclaration that))
            return false;
        return Objects.equals(delegate, that.delegate) && Objects.equals(isWildcard, that.isWildcard) && Objects.equals(isBreak, that.isBreak) && Objects.equals(isContinue, that.isContinue) && Objects.equals(isReturn, that.isReturn);
    }

    @Override()
    public String toString() {
        return "CcatchNonstandardParameterDeclaration[delegate=%s, isWildcard=%s, isBreak=%s, isContinue=%s, isReturn=%s, positionInfo=%s]".formatted(delegate, isWildcard, isBreak, isContinue, isReturn, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(delegate, isWildcard, isBreak, isContinue, isReturn);
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
