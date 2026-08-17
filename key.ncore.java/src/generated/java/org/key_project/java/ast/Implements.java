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
public final class Implements extends JavaSourceElement implements InheritanceSpecification {

    private final ImmutableList<TypeReference> typeRefs;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final ImmutableList<TypeReference> supertypes;

    public ImmutableList<TypeReference> typeRefs() {
        return typeRefs;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public ImmutableList<TypeReference> supertypes() {
        return supertypes;
    }

    public Implements(ImmutableList<TypeReference> typeRefs, @EqEx @Nullable PositionInfo positionInfo, ImmutableList<TypeReference> supertypes) {
        this.typeRefs = Objects.requireNonNull(typeRefs);
        this.positionInfo = positionInfo;
        this.supertypes = Objects.requireNonNull(supertypes);
    }

    public Implements(ImmutableList<TypeReference> typeRefs, ImmutableList<TypeReference> supertypes) {
        this.typeRefs = Objects.requireNonNull(typeRefs);
        this.positionInfo = null;
        this.supertypes = Objects.requireNonNull(supertypes);
    }

    public Implements(Implements other) {
        this(other.typeRefs, other.positionInfo, other.supertypes);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Implements other))
            return null;
        cond = MatchHelper.match(typeRefs, other.typeRefs, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(supertypes, other.supertypes, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Implements withTypeRefs(ImmutableList<TypeReference> typeRefs) {
        return new Implements(typeRefs, positionInfo(), supertypes());
    }

    public Implements withPositionInfo(PositionInfo positionInfo) {
        return new Implements(typeRefs(), positionInfo, supertypes());
    }

    public Implements withSupertypes(ImmutableList<TypeReference> supertypes) {
        return new Implements(typeRefs(), positionInfo(), supertypes);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<TypeReference> typeRefs;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public ImmutableList<TypeReference> supertypes;

        public Implements build() {
            return new Implements(typeRefs, positionInfo, supertypes);
        }

        public Builder typeRefs(ImmutableList<TypeReference> typeRefs) {
            this.typeRefs = typeRefs;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder supertypes(ImmutableList<TypeReference> supertypes) {
            this.supertypes = supertypes;
            return this;
        }

        public Builder typeRefs(TypeReference typeRefs) {
            if (this.typeRefs == null)
                this.typeRefs = new ArrayList<>();
            this.typeRefs.add(typeRefs);
            return this;
        }

        public Builder supertypes(TypeReference supertypes) {
            if (this.supertypes == null)
                this.supertypes = new ArrayList<>();
            this.supertypes.add(supertypes);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.typeRefs = typeRefs;
        b.positionInfo = positionInfo;
        b.supertypes = supertypes;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Implements that))
            return false;
        return Objects.equals(typeRefs, that.typeRefs) && Objects.equals(supertypes, that.supertypes);
    }

    @Override()
    public String toString() {
        return "Implements[typeRefs=%s, positionInfo=%s, supertypes=%s]".formatted(typeRefs, positionInfo, supertypes);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(typeRefs, supertypes);
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
