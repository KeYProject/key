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
public final class ArrayLengthReference extends JavaSourceElement implements JavaProgramElement {

    private final ReferencePrefix prefix;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ReferencePrefix prefix() {
        return prefix;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ArrayLengthReference(ReferencePrefix prefix, @EqEx @Nullable PositionInfo positionInfo) {
        this.prefix = Objects.requireNonNull(prefix);
        this.positionInfo = positionInfo;
    }

    public ArrayLengthReference(ReferencePrefix prefix) {
        this.prefix = Objects.requireNonNull(prefix);
        this.positionInfo = null;
    }

    public ArrayLengthReference(ArrayLengthReference other) {
        this(other.prefix, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ArrayLengthReference other))
            return null;
        cond = MatchHelper.match(prefix, other.prefix, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ArrayLengthReference withPrefix(ReferencePrefix prefix) {
        return new ArrayLengthReference(prefix, positionInfo());
    }

    public ArrayLengthReference withPositionInfo(PositionInfo positionInfo) {
        return new ArrayLengthReference(prefix(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ReferencePrefix prefix;

        @Nullable()
        public PositionInfo positionInfo;

        public ArrayLengthReference build() {
            return new ArrayLengthReference(prefix, positionInfo);
        }

        public Builder prefix(ReferencePrefix prefix) {
            this.prefix = prefix;
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
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ArrayLengthReference that))
            return false;
        return Objects.equals(prefix, that.prefix);
    }

    @Override()
    public String toString() {
        return "ArrayLengthReference[prefix=%s, positionInfo=%s]".formatted(prefix, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(prefix);
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
