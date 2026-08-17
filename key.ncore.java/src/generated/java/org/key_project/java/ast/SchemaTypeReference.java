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
public final class SchemaTypeReference extends JavaSourceElement implements TypeReferenceImp {

    private final int dimensions;

    private final ProgramElementName name;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final ReferencePrefix prefix;

    @java.lang.Override()
    public int dimensions() {
        return dimensions;
    }

    @java.lang.Override()
    public ProgramElementName name() {
        return name;
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

    public SchemaTypeReference(int dimensions, ProgramElementName name, @EqEx @Nullable PositionInfo positionInfo, ReferencePrefix prefix) {
        this.dimensions = Objects.requireNonNull(dimensions);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = positionInfo;
        this.prefix = Objects.requireNonNull(prefix);
    }

    public SchemaTypeReference(int dimensions, ProgramElementName name, ReferencePrefix prefix) {
        this.dimensions = Objects.requireNonNull(dimensions);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = null;
        this.prefix = Objects.requireNonNull(prefix);
    }

    public SchemaTypeReference(SchemaTypeReference other) {
        this(other.dimensions, other.name, other.positionInfo, other.prefix);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof SchemaTypeReference other))
            return null;
        cond = MatchHelper.match(dimensions, other.dimensions, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(prefix, other.prefix, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public SchemaTypeReference withDimensions(int dimensions) {
        return new SchemaTypeReference(dimensions, name(), positionInfo(), prefix());
    }

    public SchemaTypeReference withName(ProgramElementName name) {
        return new SchemaTypeReference(dimensions(), name, positionInfo(), prefix());
    }

    public SchemaTypeReference withPositionInfo(PositionInfo positionInfo) {
        return new SchemaTypeReference(dimensions(), name(), positionInfo, prefix());
    }

    public SchemaTypeReference withPrefix(ReferencePrefix prefix) {
        return new SchemaTypeReference(dimensions(), name(), positionInfo(), prefix);
    }

    public final static class Builder {

        @Nullable()
        public int dimensions;

        @Nullable()
        public ProgramElementName name;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public ReferencePrefix prefix;

        public SchemaTypeReference build() {
            return new SchemaTypeReference(dimensions, name, positionInfo, prefix);
        }

        public Builder dimensions(int dimensions) {
            this.dimensions = dimensions;
            return this;
        }

        public Builder name(ProgramElementName name) {
            this.name = name;
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
    }

    public Builder builder() {
        Builder b = new Builder();
        b.dimensions = dimensions;
        b.name = name;
        b.positionInfo = positionInfo;
        b.prefix = prefix;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SchemaTypeReference that))
            return false;
        return Objects.equals(dimensions, that.dimensions) && Objects.equals(name, that.name) && Objects.equals(prefix, that.prefix);
    }

    @Override()
    public String toString() {
        return "SchemaTypeReference[dimensions=%s, name=%s, positionInfo=%s, prefix=%s]".formatted(dimensions, name, positionInfo, prefix);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(dimensions, name, prefix);
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
