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
public final class LocalVariableDeclaration extends JavaSourceElement implements VariableDeclaration {

    private final ImmutableList<VariableSpecification> varSpecs;

    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final TypeReference typeReference;

    public ImmutableList<VariableSpecification> varSpecs() {
        return varSpecs;
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

    public LocalVariableDeclaration(ImmutableList<VariableSpecification> varSpecs, boolean parentIsInterfaceDeclaration, @EqEx @Nullable PositionInfo positionInfo, TypeReference typeReference) {
        this.varSpecs = Objects.requireNonNull(varSpecs);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public LocalVariableDeclaration(ImmutableList<VariableSpecification> varSpecs, boolean parentIsInterfaceDeclaration, TypeReference typeReference) {
        this.varSpecs = Objects.requireNonNull(varSpecs);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public LocalVariableDeclaration(LocalVariableDeclaration other) {
        this(other.varSpecs, other.parentIsInterfaceDeclaration, other.positionInfo, other.typeReference);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof LocalVariableDeclaration other))
            return null;
        cond = MatchHelper.match(varSpecs, other.varSpecs, cond);
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

    public LocalVariableDeclaration withVarSpecs(ImmutableList<VariableSpecification> varSpecs) {
        return new LocalVariableDeclaration(varSpecs, parentIsInterfaceDeclaration(), positionInfo(), typeReference());
    }

    public LocalVariableDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new LocalVariableDeclaration(varSpecs(), parentIsInterfaceDeclaration, positionInfo(), typeReference());
    }

    public LocalVariableDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new LocalVariableDeclaration(varSpecs(), parentIsInterfaceDeclaration(), positionInfo, typeReference());
    }

    public LocalVariableDeclaration withTypeReference(TypeReference typeReference) {
        return new LocalVariableDeclaration(varSpecs(), parentIsInterfaceDeclaration(), positionInfo(), typeReference);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<VariableSpecification> varSpecs;

        @Nullable()
        public boolean parentIsInterfaceDeclaration;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public TypeReference typeReference;

        public LocalVariableDeclaration build() {
            return new LocalVariableDeclaration(varSpecs, parentIsInterfaceDeclaration, positionInfo, typeReference);
        }

        public Builder varSpecs(ImmutableList<VariableSpecification> varSpecs) {
            this.varSpecs = varSpecs;
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

        public Builder varSpecs(VariableSpecification varSpecs) {
            if (this.varSpecs == null) {
                this.varSpecs = ImmutableList.of(varSpecs);
                return this;
            }
            this.varSpecs = this.varSpecs.append(varSpecs);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.varSpecs = varSpecs;
        b.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
        b.positionInfo = positionInfo;
        b.typeReference = typeReference;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof LocalVariableDeclaration that))
            return false;
        return Objects.equals(varSpecs, that.varSpecs) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration) && Objects.equals(typeReference, that.typeReference);
    }

    @Override()
    public String toString() {
        return "LocalVariableDeclaration[varSpecs=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s, typeReference=%s]".formatted(varSpecs, parentIsInterfaceDeclaration, positionInfo, typeReference);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(varSpecs, parentIsInterfaceDeclaration, typeReference);
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
