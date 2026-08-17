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
public final class Continue extends JavaSourceElement implements LabelJumpStatement {

    private final Label name;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @java.lang.Override()
    public Label name() {
        return name;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Continue(Label name, @EqEx @Nullable PositionInfo positionInfo) {
        this.name = Objects.requireNonNull(name);
        this.positionInfo = positionInfo;
    }

    public Continue(Label name) {
        this.name = Objects.requireNonNull(name);
        this.positionInfo = null;
    }

    public Continue(Continue other) {
        this(other.name, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Continue other))
            return null;
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Continue withName(Label name) {
        return new Continue(name, positionInfo());
    }

    public Continue withPositionInfo(PositionInfo positionInfo) {
        return new Continue(name(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Label name;

        @Nullable()
        public PositionInfo positionInfo;

        public Continue build() {
            return new Continue(name, positionInfo);
        }

        public Builder name(Label name) {
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
        b.name = name;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Continue that))
            return false;
        return Objects.equals(name, that.name);
    }

    @Override()
    public String toString() {
        return "Continue[name=%s, positionInfo=%s]".formatted(name, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(name);
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
