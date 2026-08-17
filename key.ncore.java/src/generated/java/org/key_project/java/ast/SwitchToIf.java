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
public final class SwitchToIf extends JavaSourceElement implements ProgramTransformer {

    private final ProgramElement body;

    private final String name;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @java.lang.Override()
    public ProgramElement body() {
        return body;
    }

    @java.lang.Override()
    public String name() {
        return name;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public SwitchToIf(ProgramElement body, String name, @EqEx @Nullable PositionInfo positionInfo) {
        this.body = Objects.requireNonNull(body);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = positionInfo;
    }

    public SwitchToIf(ProgramElement body, String name) {
        this.body = Objects.requireNonNull(body);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = null;
    }

    public SwitchToIf(SwitchToIf other) {
        this(other.body, other.name, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof SwitchToIf other))
            return null;
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public SwitchToIf withBody(ProgramElement body) {
        return new SwitchToIf(body, name(), positionInfo());
    }

    public SwitchToIf withName(String name) {
        return new SwitchToIf(body(), name, positionInfo());
    }

    public SwitchToIf withPositionInfo(PositionInfo positionInfo) {
        return new SwitchToIf(body(), name(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ProgramElement body;

        @Nullable()
        public String name;

        @Nullable()
        public PositionInfo positionInfo;

        public SwitchToIf build() {
            return new SwitchToIf(body, name, positionInfo);
        }

        public Builder body(ProgramElement body) {
            this.body = body;
            return this;
        }

        public Builder name(String name) {
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
        b.body = body;
        b.name = name;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SwitchToIf that))
            return false;
        return Objects.equals(body, that.body) && Objects.equals(name, that.name);
    }

    @Override()
    public String toString() {
        return "SwitchToIf[body=%s, name=%s, positionInfo=%s]".formatted(body, name, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(body, name);
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
