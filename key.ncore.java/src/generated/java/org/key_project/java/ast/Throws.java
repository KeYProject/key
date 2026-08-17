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
public final class Throws extends JavaSourceElement implements JavaProgramElement {

    private final ImmutableList<TypeReference> exceptions;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ImmutableList<TypeReference> exceptions() {
        return exceptions;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Throws(ImmutableList<TypeReference> exceptions, @EqEx @Nullable PositionInfo positionInfo) {
        this.exceptions = Objects.requireNonNull(exceptions);
        this.positionInfo = positionInfo;
    }

    public Throws(ImmutableList<TypeReference> exceptions) {
        this.exceptions = Objects.requireNonNull(exceptions);
        this.positionInfo = null;
    }

    public Throws(Throws other) {
        this(other.exceptions, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Throws other))
            return null;
        cond = MatchHelper.match(exceptions, other.exceptions, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Throws withExceptions(ImmutableList<TypeReference> exceptions) {
        return new Throws(exceptions, positionInfo());
    }

    public Throws withPositionInfo(PositionInfo positionInfo) {
        return new Throws(exceptions(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<TypeReference> exceptions;

        @Nullable()
        public PositionInfo positionInfo;

        public Throws build() {
            return new Throws(exceptions, positionInfo);
        }

        public Builder exceptions(ImmutableList<TypeReference> exceptions) {
            this.exceptions = exceptions;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder exceptions(TypeReference exceptions) {
            if (this.exceptions == null)
                this.exceptions = new ArrayList<>();
            this.exceptions.add(exceptions);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.exceptions = exceptions;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Throws that))
            return false;
        return Objects.equals(exceptions, that.exceptions);
    }

    @Override()
    public String toString() {
        return "Throws[exceptions=%s, positionInfo=%s]".formatted(exceptions, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(exceptions);
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
