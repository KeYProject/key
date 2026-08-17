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
public final class ExactInstanceof extends JavaSourceElement implements TypeOperator {

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final TypeReference typeReference;

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public TypeReference typeReference() {
        return typeReference;
    }

    public ExactInstanceof(@EqEx @Nullable PositionInfo positionInfo, TypeReference typeReference) {
        this.positionInfo = positionInfo;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public ExactInstanceof(TypeReference typeReference) {
        this.positionInfo = null;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public ExactInstanceof(ExactInstanceof other) {
        this(other.positionInfo, other.typeReference);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ExactInstanceof other))
            return null;
        cond = MatchHelper.match(typeReference, other.typeReference, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ExactInstanceof withPositionInfo(PositionInfo positionInfo) {
        return new ExactInstanceof(positionInfo, typeReference());
    }

    public ExactInstanceof withTypeReference(TypeReference typeReference) {
        return new ExactInstanceof(positionInfo(), typeReference);
    }

    public final static class Builder {

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public TypeReference typeReference;

        public ExactInstanceof build() {
            return new ExactInstanceof(positionInfo, typeReference);
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder typeReference(TypeReference typeReference) {
            this.typeReference = typeReference;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.positionInfo = positionInfo;
        b.typeReference = typeReference;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ExactInstanceof that))
            return false;
        return Objects.equals(typeReference, that.typeReference);
    }

    @Override()
    public String toString() {
        return "ExactInstanceof[positionInfo=%s, typeReference=%s]".formatted(positionInfo, typeReference);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(typeReference);
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
