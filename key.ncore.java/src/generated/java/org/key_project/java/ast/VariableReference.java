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
public final class VariableReference extends JavaSourceElement implements JavaProgramElement {

    private final ProgramVariable variable;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ProgramVariable variable() {
        return variable;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public VariableReference(ProgramVariable variable, @EqEx @Nullable PositionInfo positionInfo) {
        this.variable = Objects.requireNonNull(variable);
        this.positionInfo = positionInfo;
    }

    public VariableReference(ProgramVariable variable) {
        this.variable = Objects.requireNonNull(variable);
        this.positionInfo = null;
    }

    public VariableReference(VariableReference other) {
        this(other.variable, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof VariableReference other))
            return null;
        cond = MatchHelper.match(variable, other.variable, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public VariableReference withVariable(ProgramVariable variable) {
        return new VariableReference(variable, positionInfo());
    }

    public VariableReference withPositionInfo(PositionInfo positionInfo) {
        return new VariableReference(variable(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ProgramVariable variable;

        @Nullable()
        public PositionInfo positionInfo;

        public VariableReference build() {
            return new VariableReference(variable, positionInfo);
        }

        public Builder variable(ProgramVariable variable) {
            this.variable = variable;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.variable = variable;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof VariableReference that))
            return false;
        return Objects.equals(variable, that.variable);
    }

    @Override()
    public String toString() {
        return "VariableReference[variable=%s, positionInfo=%s]".formatted(variable, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(variable);
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
