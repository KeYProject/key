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
public final class SchematicFieldReference extends JavaSourceElement implements FieldReference {

    private final SchemaVariable schemaVariable;

    @EqEx
    @Nullable
    @java.lang.Override()
    private final PositionInfo positionInfo;

    private final ReferencePrefix prefix;

    @java.lang.Override()
    private final ProgramVariable variable;

    public SchemaVariable schemaVariable() {
        return schemaVariable;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public ReferencePrefix prefix() {
        return prefix;
    }

    @java.lang.Override()
    public ProgramVariable variable() {
        return variable;
    }

    public SchematicFieldReference(SchemaVariable schemaVariable, @EqEx @Nullable @java.lang.Override() PositionInfo positionInfo, ReferencePrefix prefix, @java.lang.Override() ProgramVariable variable) {
        this.schemaVariable = Objects.requireNonNull(schemaVariable);
        this.positionInfo = positionInfo;
        this.prefix = Objects.requireNonNull(prefix);
        this.variable = Objects.requireNonNull(variable);
    }

    public SchematicFieldReference(SchemaVariable schemaVariable, ReferencePrefix prefix, @java.lang.Override() ProgramVariable variable) {
        this.schemaVariable = Objects.requireNonNull(schemaVariable);
        this.positionInfo = null;
        this.prefix = Objects.requireNonNull(prefix);
        this.variable = Objects.requireNonNull(variable);
    }

    public SchematicFieldReference(SchematicFieldReference other) {
        this(other.schemaVariable, other.positionInfo, other.prefix, other.variable);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof SchematicFieldReference other))
            return null;
        cond = MatchHelper.match(schemaVariable, other.schemaVariable, cond);
        if (cond == null) {
            return null;
        }
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

    public SchematicFieldReference withSchemaVariable(SchemaVariable schemaVariable) {
        return new SchematicFieldReference(schemaVariable, positionInfo(), prefix(), variable());
    }

    public SchematicFieldReference withPositionInfo(PositionInfo positionInfo) {
        return new SchematicFieldReference(schemaVariable(), positionInfo, prefix(), variable());
    }

    public SchematicFieldReference withPrefix(ReferencePrefix prefix) {
        return new SchematicFieldReference(schemaVariable(), positionInfo(), prefix, variable());
    }

    public SchematicFieldReference withVariable(ProgramVariable variable) {
        return new SchematicFieldReference(schemaVariable(), positionInfo(), prefix(), variable);
    }

    public final static class Builder {

        @Nullable()
        public SchemaVariable schemaVariable;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public ReferencePrefix prefix;

        @Nullable()
        public ProgramVariable variable;

        public SchematicFieldReference build() {
            return new SchematicFieldReference(schemaVariable, positionInfo, prefix, variable);
        }

        public Builder schemaVariable(SchemaVariable schemaVariable) {
            this.schemaVariable = schemaVariable;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder prefix(ReferencePrefix prefix) {
            this.prefix = prefix;
            return this;
        }

        public Builder variable(ProgramVariable variable) {
            this.variable = variable;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.schemaVariable = schemaVariable;
        b.positionInfo = positionInfo;
        b.prefix = prefix;
        b.variable = variable;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SchematicFieldReference that))
            return false;
        return Objects.equals(schemaVariable, that.schemaVariable) && Objects.equals(prefix, that.prefix) && Objects.equals(variable, that.variable);
    }

    @Override()
    public String toString() {
        return "SchematicFieldReference[schemaVariable=%s, positionInfo=%s, prefix=%s, variable=%s]".formatted(schemaVariable, positionInfo, prefix, variable);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(schemaVariable, prefix, variable);
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
