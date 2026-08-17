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
public final class Import extends JavaSourceElement implements JavaProgramElement {

    private final boolean isMultiImport;

    private final boolean isStatic;

    private final TypeReferenceInfix reference;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public boolean isMultiImport() {
        return isMultiImport;
    }

    public boolean isStatic() {
        return isStatic;
    }

    public TypeReferenceInfix reference() {
        return reference;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Import(boolean isMultiImport, boolean isStatic, TypeReferenceInfix reference, @EqEx @Nullable PositionInfo positionInfo) {
        this.isMultiImport = Objects.requireNonNull(isMultiImport);
        this.isStatic = Objects.requireNonNull(isStatic);
        this.reference = Objects.requireNonNull(reference);
        this.positionInfo = positionInfo;
    }

    public Import(boolean isMultiImport, boolean isStatic, TypeReferenceInfix reference) {
        this.isMultiImport = Objects.requireNonNull(isMultiImport);
        this.isStatic = Objects.requireNonNull(isStatic);
        this.reference = Objects.requireNonNull(reference);
        this.positionInfo = null;
    }

    public Import(Import other) {
        this(other.isMultiImport, other.isStatic, other.reference, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Import other))
            return null;
        cond = MatchHelper.match(isMultiImport, other.isMultiImport, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isStatic, other.isStatic, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(reference, other.reference, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Import withIsMultiImport(boolean isMultiImport) {
        return new Import(isMultiImport, isStatic(), reference(), positionInfo());
    }

    public Import withIsStatic(boolean isStatic) {
        return new Import(isMultiImport(), isStatic, reference(), positionInfo());
    }

    public Import withReference(TypeReferenceInfix reference) {
        return new Import(isMultiImport(), isStatic(), reference, positionInfo());
    }

    public Import withPositionInfo(PositionInfo positionInfo) {
        return new Import(isMultiImport(), isStatic(), reference(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public boolean isMultiImport;

        @Nullable()
        public boolean isStatic;

        @Nullable()
        public TypeReferenceInfix reference;

        @Nullable()
        public PositionInfo positionInfo;

        public Import build() {
            return new Import(isMultiImport, isStatic, reference, positionInfo);
        }

        public Builder isMultiImport(boolean isMultiImport) {
            this.isMultiImport = isMultiImport;
            return this;
        }

        public Builder isStatic(boolean isStatic) {
            this.isStatic = isStatic;
            return this;
        }

        public Builder reference(TypeReferenceInfix reference) {
            this.reference = reference;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.isMultiImport = isMultiImport;
        b.isStatic = isStatic;
        b.reference = reference;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Import that))
            return false;
        return Objects.equals(isMultiImport, that.isMultiImport) && Objects.equals(isStatic, that.isStatic) && Objects.equals(reference, that.reference);
    }

    @Override()
    public String toString() {
        return "Import[isMultiImport=%s, isStatic=%s, reference=%s, positionInfo=%s]".formatted(isMultiImport, isStatic, reference, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(isMultiImport, isStatic, reference);
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
