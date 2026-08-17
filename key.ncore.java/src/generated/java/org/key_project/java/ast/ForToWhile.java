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
public final class ForToWhile extends JavaSourceElement implements ProgramTransformer {

    private final SchemaVariable innerLabel;

    private final SchemaVariable outerLabel;

    private final Statement body;

    private final String name = "#for-to-while";

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public SchemaVariable innerLabel() {
        return innerLabel;
    }

    public SchemaVariable outerLabel() {
        return outerLabel;
    }

    public Statement body() {
        return body;
    }

    public String name() {
        return name;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ForToWhile(SchemaVariable innerLabel, SchemaVariable outerLabel, Statement body, @EqEx @Nullable PositionInfo positionInfo) {
        this.innerLabel = Objects.requireNonNull(innerLabel);
        this.outerLabel = Objects.requireNonNull(outerLabel);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public ForToWhile(SchemaVariable innerLabel, SchemaVariable outerLabel, Statement body) {
        this.innerLabel = Objects.requireNonNull(innerLabel);
        this.outerLabel = Objects.requireNonNull(outerLabel);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public ForToWhile(ForToWhile other) {
        this(other.innerLabel, other.outerLabel, other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ForToWhile other))
            return null;
        cond = MatchHelper.match(innerLabel, other.innerLabel, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(outerLabel, other.outerLabel, cond);
        if (cond == null) {
            return null;
        }
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

    public ForToWhile withInnerLabel(SchemaVariable innerLabel) {
        return new ForToWhile(innerLabel, outerLabel(), body(), name(), positionInfo());
    }

    public ForToWhile withOuterLabel(SchemaVariable outerLabel) {
        return new ForToWhile(innerLabel(), outerLabel, body(), name(), positionInfo());
    }

    public ForToWhile withBody(Statement body) {
        return new ForToWhile(innerLabel(), outerLabel(), body, name(), positionInfo());
    }

    public ForToWhile withPositionInfo(PositionInfo positionInfo) {
        return new ForToWhile(innerLabel(), outerLabel(), body(), name(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public SchemaVariable innerLabel;

        @Nullable()
        public SchemaVariable outerLabel;

        @Nullable()
        public Statement body;

        @Nullable()
        public PositionInfo positionInfo;

        public ForToWhile build() {
            return new ForToWhile(innerLabel, outerLabel, body, positionInfo);
        }

        public Builder innerLabel(SchemaVariable innerLabel) {
            this.innerLabel = innerLabel;
            return this;
        }

        public Builder outerLabel(SchemaVariable outerLabel) {
            this.outerLabel = outerLabel;
            return this;
        }

        public Builder body(Statement body) {
            this.body = body;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.innerLabel = innerLabel;
        b.outerLabel = outerLabel;
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ForToWhile that))
            return false;
        return Objects.equals(innerLabel, that.innerLabel) && Objects.equals(outerLabel, that.outerLabel) && Objects.equals(body, that.body) && Objects.equals(name, that.name);
    }

    @Override()
    public String toString() {
        return "ForToWhile[innerLabel=%s, outerLabel=%s, body=%s, name=%s, positionInfo=%s]".formatted(innerLabel, outerLabel, body, name, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(innerLabel, outerLabel, body, name);
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
