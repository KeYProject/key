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
public final class FieldReference extends JavaSourceElement implements VariableReference {

    private final ReferencePrefix prefix;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final ProgramVariable variable;

    public ReferencePrefix prefix() {
        return prefix;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public ProgramVariable variable() {
        return variable;
    }

    public FieldReference(ReferencePrefix prefix, @EqEx @Nullable PositionInfo positionInfo, ProgramVariable variable) {
        this.prefix = Objects.requireNonNull(prefix);
        this.positionInfo = positionInfo;
        this.variable = Objects.requireNonNull(variable);
    }

    public FieldReference(ReferencePrefix prefix, ProgramVariable variable) {
        this.prefix = Objects.requireNonNull(prefix);
        this.positionInfo = null;
        this.variable = Objects.requireNonNull(variable);
    }

    public FieldReference(FieldReference other) {
        this(other.prefix, other.positionInfo, other.variable);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof FieldReference other))
            return null;
        cond = MatchHelper.match(prefix, other.prefix, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(variable, other.variable, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public FieldReference withPrefix(ReferencePrefix prefix) {
        return new FieldReference(prefix, positionInfo(), variable());
    }

    public FieldReference withPositionInfo(PositionInfo positionInfo) {
        return new FieldReference(prefix(), positionInfo, variable());
    }

    public FieldReference withVariable(ProgramVariable variable) {
        return new FieldReference(prefix(), positionInfo(), variable);
    }

    public final static class Builder {

        @Nullable()
        public ReferencePrefix prefix;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public ProgramVariable variable;

        public FieldReference build() {
            return new FieldReference(prefix, positionInfo, variable);
        }

        public Builder prefix(ReferencePrefix prefix) {
            this.prefix = prefix;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder variable(ProgramVariable variable) {
            this.variable = variable;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.prefix = prefix;
        b.positionInfo = positionInfo;
        b.variable = variable;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FieldReference that))
            return false;
        return Objects.equals(prefix, that.prefix) && Objects.equals(variable, that.variable);
    }

    @Override()
    public String toString() {
        return "FieldReference[prefix=%s, positionInfo=%s, variable=%s]".formatted(prefix, positionInfo, variable);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(prefix, variable);
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
