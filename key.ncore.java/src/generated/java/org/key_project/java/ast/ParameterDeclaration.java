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
public final class ParameterDeclaration extends JavaSourceElement implements VariableDeclaration {

    private final ImmutableList<VariableSpecification> varSpec;

    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final TypeReference typeReference;

    public ImmutableList<VariableSpecification> varSpec() {
        return varSpec;
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

    public ParameterDeclaration(ImmutableList<VariableSpecification> varSpec, boolean parentIsInterfaceDeclaration, @EqEx @Nullable PositionInfo positionInfo, TypeReference typeReference) {
        this.varSpec = Objects.requireNonNull(varSpec);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public ParameterDeclaration(ImmutableList<VariableSpecification> varSpec, boolean parentIsInterfaceDeclaration, TypeReference typeReference) {
        this.varSpec = Objects.requireNonNull(varSpec);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public ParameterDeclaration(ParameterDeclaration other) {
        this(other.varSpec, other.parentIsInterfaceDeclaration, other.positionInfo, other.typeReference);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ParameterDeclaration other))
            return null;
        cond = MatchHelper.match(varSpec, other.varSpec, cond);
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

    public ParameterDeclaration withVarSpec(ImmutableList<VariableSpecification> varSpec) {
        return new ParameterDeclaration(varSpec, parentIsInterfaceDeclaration(), positionInfo(), typeReference());
    }

    public ParameterDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new ParameterDeclaration(varSpec(), parentIsInterfaceDeclaration, positionInfo(), typeReference());
    }

    public ParameterDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new ParameterDeclaration(varSpec(), parentIsInterfaceDeclaration(), positionInfo, typeReference());
    }

    public ParameterDeclaration withTypeReference(TypeReference typeReference) {
        return new ParameterDeclaration(varSpec(), parentIsInterfaceDeclaration(), positionInfo(), typeReference);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<VariableSpecification> varSpec;

        @Nullable()
        public boolean parentIsInterfaceDeclaration;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public TypeReference typeReference;

        public ParameterDeclaration build() {
            return new ParameterDeclaration(varSpec, parentIsInterfaceDeclaration, positionInfo, typeReference);
        }

        public Builder varSpec(ImmutableList<VariableSpecification> varSpec) {
            this.varSpec = varSpec;
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

        public Builder varSpec(VariableSpecification varSpec) {
            if (this.varSpec == null)
                this.varSpec = new ArrayList<>();
            this.varSpec.add(varSpec);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.varSpec = varSpec;
        b.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
        b.positionInfo = positionInfo;
        b.typeReference = typeReference;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ParameterDeclaration that))
            return false;
        return Objects.equals(varSpec, that.varSpec) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration) && Objects.equals(typeReference, that.typeReference);
    }

    @Override()
    public String toString() {
        return "ParameterDeclaration[varSpec=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s, typeReference=%s]".formatted(varSpec, parentIsInterfaceDeclaration, positionInfo, typeReference);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(varSpec, parentIsInterfaceDeclaration, typeReference);
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
