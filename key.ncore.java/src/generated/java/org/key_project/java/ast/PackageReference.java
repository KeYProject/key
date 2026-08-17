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
public final class PackageReference extends JavaSourceElement implements JavaProgramElement {

    private final ReferencePrefix prefix;

    private final ProgramElementName name;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ReferencePrefix prefix() {
        return prefix;
    }

    public ProgramElementName name() {
        return name;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public PackageReference(ReferencePrefix prefix, ProgramElementName name, @EqEx @Nullable PositionInfo positionInfo) {
        this.prefix = Objects.requireNonNull(prefix);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = positionInfo;
    }

    public PackageReference(ReferencePrefix prefix, ProgramElementName name) {
        this.prefix = Objects.requireNonNull(prefix);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = null;
    }

    public PackageReference(PackageReference other) {
        this(other.prefix, other.name, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof PackageReference other))
            return null;
        cond = MatchHelper.match(prefix, other.prefix, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public PackageReference withPrefix(ReferencePrefix prefix) {
        return new PackageReference(prefix, name(), positionInfo());
    }

    public PackageReference withName(ProgramElementName name) {
        return new PackageReference(prefix(), name, positionInfo());
    }

    public PackageReference withPositionInfo(PositionInfo positionInfo) {
        return new PackageReference(prefix(), name(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ReferencePrefix prefix;

        @Nullable()
        public ProgramElementName name;

        @Nullable()
        public PositionInfo positionInfo;

        public PackageReference build() {
            return new PackageReference(prefix, name, positionInfo);
        }

        public Builder prefix(ReferencePrefix prefix) {
            this.prefix = prefix;
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
    }

    public Builder builder() {
        Builder b = new Builder();
        b.prefix = prefix;
        b.name = name;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof PackageReference that))
            return false;
        return Objects.equals(prefix, that.prefix) && Objects.equals(name, that.name);
    }

    @Override()
    public String toString() {
        return "PackageReference[prefix=%s, name=%s, positionInfo=%s]".formatted(prefix, name, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(prefix, name);
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
