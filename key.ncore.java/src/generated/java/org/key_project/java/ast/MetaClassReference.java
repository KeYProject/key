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
public final class MetaClassReference extends JavaSourceElement implements JavaProgramElement {

    private final TypeReference typeReference;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public TypeReference typeReference() {
        return typeReference;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public MetaClassReference(TypeReference typeReference, @EqEx @Nullable PositionInfo positionInfo) {
        this.typeReference = Objects.requireNonNull(typeReference);
        this.positionInfo = positionInfo;
    }

    public MetaClassReference(TypeReference typeReference) {
        this.typeReference = Objects.requireNonNull(typeReference);
        this.positionInfo = null;
    }

    public MetaClassReference(MetaClassReference other) {
        this(other.typeReference, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof MetaClassReference other))
            return null;
        cond = MatchHelper.match(typeReference, other.typeReference, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public MetaClassReference withTypeReference(TypeReference typeReference) {
        return new MetaClassReference(typeReference, positionInfo());
    }

    public MetaClassReference withPositionInfo(PositionInfo positionInfo) {
        return new MetaClassReference(typeReference(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public TypeReference typeReference;

        @Nullable()
        public PositionInfo positionInfo;

        public MetaClassReference build() {
            return new MetaClassReference(typeReference, positionInfo);
        }

        public Builder typeReference(TypeReference typeReference) {
            this.typeReference = typeReference;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.typeReference = typeReference;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof MetaClassReference that))
            return false;
        return Objects.equals(typeReference, that.typeReference);
    }

    @Override()
    public String toString() {
        return "MetaClassReference[typeReference=%s, positionInfo=%s]".formatted(typeReference, positionInfo);
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
