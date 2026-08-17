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
public final class New extends JavaSourceElement implements TypeOperator {

    private final ClassDeclaration anonymousClass;

    private final ReferencePrefix accessPath;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final TypeReference typeReference;

    public ClassDeclaration anonymousClass() {
        return anonymousClass;
    }

    public ReferencePrefix accessPath() {
        return accessPath;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public TypeReference typeReference() {
        return typeReference;
    }

    public New(ClassDeclaration anonymousClass, ReferencePrefix accessPath, @EqEx @Nullable PositionInfo positionInfo, TypeReference typeReference) {
        this.anonymousClass = Objects.requireNonNull(anonymousClass);
        this.accessPath = Objects.requireNonNull(accessPath);
        this.positionInfo = positionInfo;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public New(ClassDeclaration anonymousClass, ReferencePrefix accessPath, TypeReference typeReference) {
        this.anonymousClass = Objects.requireNonNull(anonymousClass);
        this.accessPath = Objects.requireNonNull(accessPath);
        this.positionInfo = null;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public New(New other) {
        this(other.anonymousClass, other.accessPath, other.positionInfo, other.typeReference);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof New other))
            return null;
        cond = MatchHelper.match(anonymousClass, other.anonymousClass, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(accessPath, other.accessPath, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(typeReference, other.typeReference, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public New withAnonymousClass(ClassDeclaration anonymousClass) {
        return new New(anonymousClass, accessPath(), positionInfo(), typeReference());
    }

    public New withAccessPath(ReferencePrefix accessPath) {
        return new New(anonymousClass(), accessPath, positionInfo(), typeReference());
    }

    public New withPositionInfo(PositionInfo positionInfo) {
        return new New(anonymousClass(), accessPath(), positionInfo, typeReference());
    }

    public New withTypeReference(TypeReference typeReference) {
        return new New(anonymousClass(), accessPath(), positionInfo(), typeReference);
    }

    public final static class Builder {

        @Nullable()
        public ClassDeclaration anonymousClass;

        @Nullable()
        public ReferencePrefix accessPath;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public TypeReference typeReference;

        public New build() {
            return new New(anonymousClass, accessPath, positionInfo, typeReference);
        }

        public Builder anonymousClass(ClassDeclaration anonymousClass) {
            this.anonymousClass = anonymousClass;
            return this;
        }

        public Builder accessPath(ReferencePrefix accessPath) {
            this.accessPath = accessPath;
            return this;
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
        b.anonymousClass = anonymousClass;
        b.accessPath = accessPath;
        b.positionInfo = positionInfo;
        b.typeReference = typeReference;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof New that))
            return false;
        return Objects.equals(anonymousClass, that.anonymousClass) && Objects.equals(accessPath, that.accessPath) && Objects.equals(typeReference, that.typeReference);
    }

    @Override()
    public String toString() {
        return "New[anonymousClass=%s, accessPath=%s, positionInfo=%s, typeReference=%s]".formatted(anonymousClass, accessPath, positionInfo, typeReference);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(anonymousClass, accessPath, typeReference);
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
