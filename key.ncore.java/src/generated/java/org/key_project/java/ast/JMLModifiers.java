package org.key_project.java.ast;

import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import java.util.*;
import org.jspecify.annotations.NullMarked;

@NullMarked()
public final class JMLModifiers extends JavaSourceElement implements JavaProgramElement {

    private final boolean strictlyPure;

    private final boolean pure;

    private final boolean nullableByDefault;

    private final boolean helper;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public boolean strictlyPure() {
        return strictlyPure;
    }

    public boolean pure() {
        return pure;
    }

    public boolean nullableByDefault() {
        return nullableByDefault;
    }

    public boolean helper() {
        return helper;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public JMLModifiers(boolean strictlyPure, boolean pure, boolean nullableByDefault, boolean helper, @EqEx @Nullable PositionInfo positionInfo) {
        this.strictlyPure = Objects.requireNonNull(strictlyPure);
        this.pure = Objects.requireNonNull(pure);
        this.nullableByDefault = Objects.requireNonNull(nullableByDefault);
        this.helper = Objects.requireNonNull(helper);
        this.positionInfo = positionInfo;
    }

    public JMLModifiers(boolean strictlyPure, boolean pure, boolean nullableByDefault, boolean helper) {
        this.strictlyPure = Objects.requireNonNull(strictlyPure);
        this.pure = Objects.requireNonNull(pure);
        this.nullableByDefault = Objects.requireNonNull(nullableByDefault);
        this.helper = Objects.requireNonNull(helper);
        this.positionInfo = null;
    }

    public JMLModifiers(JMLModifiers other) {
        this(other.strictlyPure, other.pure, other.nullableByDefault, other.helper, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof JMLModifiers other))
            return null;
        cond = MatchHelper.match(strictlyPure, other.strictlyPure, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(pure, other.pure, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(nullableByDefault, other.nullableByDefault, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(helper, other.helper, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public JMLModifiers withStrictlyPure(boolean strictlyPure) {
        return new JMLModifiers(strictlyPure, pure(), nullableByDefault(), helper(), positionInfo());
    }

    public JMLModifiers withPure(boolean pure) {
        return new JMLModifiers(strictlyPure(), pure, nullableByDefault(), helper(), positionInfo());
    }

    public JMLModifiers withNullableByDefault(boolean nullableByDefault) {
        return new JMLModifiers(strictlyPure(), pure(), nullableByDefault, helper(), positionInfo());
    }

    public JMLModifiers withHelper(boolean helper) {
        return new JMLModifiers(strictlyPure(), pure(), nullableByDefault(), helper, positionInfo());
    }

    public JMLModifiers withPositionInfo(PositionInfo positionInfo) {
        return new JMLModifiers(strictlyPure(), pure(), nullableByDefault(), helper(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public boolean strictlyPure;

        @Nullable()
        public boolean pure;

        @Nullable()
        public boolean nullableByDefault;

        @Nullable()
        public boolean helper;

        @Nullable()
        public PositionInfo positionInfo;

        public JMLModifiers build() {
            return new JMLModifiers(strictlyPure, pure, nullableByDefault, helper, positionInfo);
        }

        public Builder strictlyPure(boolean strictlyPure) {
            this.strictlyPure = strictlyPure;
            return this;
        }

        public Builder pure(boolean pure) {
            this.pure = pure;
            return this;
        }

        public Builder nullableByDefault(boolean nullableByDefault) {
            this.nullableByDefault = nullableByDefault;
            return this;
        }

        public Builder helper(boolean helper) {
            this.helper = helper;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.strictlyPure = strictlyPure;
        b.pure = pure;
        b.nullableByDefault = nullableByDefault;
        b.helper = helper;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof JMLModifiers that))
            return false;
        return Objects.equals(strictlyPure, that.strictlyPure) && Objects.equals(pure, that.pure) && Objects.equals(nullableByDefault, that.nullableByDefault) && Objects.equals(helper, that.helper);
    }

    @Override()
    public String toString() {
        return "JMLModifiers[strictlyPure=%s, pure=%s, nullableByDefault=%s, helper=%s, positionInfo=%s]".formatted(strictlyPure, pure, nullableByDefault, helper, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(strictlyPure, pure, nullableByDefault, helper);
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
