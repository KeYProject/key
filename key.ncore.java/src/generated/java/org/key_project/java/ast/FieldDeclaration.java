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
public final class FieldDeclaration extends JavaSourceElement implements VariableDeclaration {

    private final ImmutableList<FieldSpecification> fieldSpecs;

    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final TypeReference typeReference;

    public ImmutableList<FieldSpecification> fieldSpecs() {
        return fieldSpecs;
    }

    @java.lang.Override()
    public boolean parentIsInterfaceDeclaration() {
        return parentIsInterfaceDeclaration;
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

    public FieldDeclaration(ImmutableList<FieldSpecification> fieldSpecs, boolean parentIsInterfaceDeclaration, @EqEx @Nullable PositionInfo positionInfo, TypeReference typeReference) {
        this.fieldSpecs = Objects.requireNonNull(fieldSpecs);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public FieldDeclaration(ImmutableList<FieldSpecification> fieldSpecs, boolean parentIsInterfaceDeclaration, TypeReference typeReference) {
        this.fieldSpecs = Objects.requireNonNull(fieldSpecs);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public FieldDeclaration(FieldDeclaration other) {
        this(other.fieldSpecs, other.parentIsInterfaceDeclaration, other.positionInfo, other.typeReference);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof FieldDeclaration other))
            return null;
        cond = MatchHelper.match(fieldSpecs, other.fieldSpecs, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(parentIsInterfaceDeclaration, other.parentIsInterfaceDeclaration, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(typeReference, other.typeReference, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public FieldDeclaration withFieldSpecs(ImmutableList<FieldSpecification> fieldSpecs) {
        return new FieldDeclaration(fieldSpecs, parentIsInterfaceDeclaration(), positionInfo(), typeReference());
    }

    public FieldDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new FieldDeclaration(fieldSpecs(), parentIsInterfaceDeclaration, positionInfo(), typeReference());
    }

    public FieldDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new FieldDeclaration(fieldSpecs(), parentIsInterfaceDeclaration(), positionInfo, typeReference());
    }

    public FieldDeclaration withTypeReference(TypeReference typeReference) {
        return new FieldDeclaration(fieldSpecs(), parentIsInterfaceDeclaration(), positionInfo(), typeReference);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<FieldSpecification> fieldSpecs;

        @Nullable()
        public boolean parentIsInterfaceDeclaration;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public TypeReference typeReference;

        public FieldDeclaration build() {
            return new FieldDeclaration(fieldSpecs, parentIsInterfaceDeclaration, positionInfo, typeReference);
        }

        public Builder fieldSpecs(ImmutableList<FieldSpecification> fieldSpecs) {
            this.fieldSpecs = fieldSpecs;
            return this;
        }

        public Builder parentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
            this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
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

        public Builder fieldSpecs(FieldSpecification fieldSpecs) {
            if (this.fieldSpecs == null)
                this.fieldSpecs = new ArrayList<>();
            this.fieldSpecs.add(fieldSpecs);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.fieldSpecs = fieldSpecs;
        b.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
        b.positionInfo = positionInfo;
        b.typeReference = typeReference;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FieldDeclaration that))
            return false;
        return Objects.equals(fieldSpecs, that.fieldSpecs) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration) && Objects.equals(typeReference, that.typeReference);
    }

    @Override()
    public String toString() {
        return "FieldDeclaration[fieldSpecs=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s, typeReference=%s]".formatted(fieldSpecs, parentIsInterfaceDeclaration, positionInfo, typeReference);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(fieldSpecs, parentIsInterfaceDeclaration, typeReference);
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
