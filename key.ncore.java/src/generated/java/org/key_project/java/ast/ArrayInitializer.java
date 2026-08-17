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
public final class ArrayInitializer extends JavaSourceElement implements JavaProgramElement {

    private final KeYJavaType kjt;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public KeYJavaType kjt() {
        return kjt;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ArrayInitializer(KeYJavaType kjt, @EqEx @Nullable PositionInfo positionInfo) {
        this.kjt = Objects.requireNonNull(kjt);
        this.positionInfo = positionInfo;
    }

    public ArrayInitializer(KeYJavaType kjt) {
        this.kjt = Objects.requireNonNull(kjt);
        this.positionInfo = null;
    }

    public ArrayInitializer(ArrayInitializer other) {
        this(other.kjt, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ArrayInitializer other))
            return null;
        cond = MatchHelper.match(kjt, other.kjt, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ArrayInitializer withKjt(KeYJavaType kjt) {
        return new ArrayInitializer(kjt, positionInfo());
    }

    public ArrayInitializer withPositionInfo(PositionInfo positionInfo) {
        return new ArrayInitializer(kjt(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public KeYJavaType kjt;

        @Nullable()
        public PositionInfo positionInfo;

        public ArrayInitializer build() {
            return new ArrayInitializer(kjt, positionInfo);
        }

        public Builder kjt(KeYJavaType kjt) {
            this.kjt = kjt;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.kjt = kjt;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ArrayInitializer that))
            return false;
        return Objects.equals(kjt, that.kjt);
    }

    @Override()
    public String toString() {
        return "ArrayInitializer[kjt=%s, positionInfo=%s]".formatted(kjt, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(kjt);
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
