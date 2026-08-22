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
public final class InitArrayCreation extends JavaSourceElement implements InitArray {

    private final SchemaVariable newObjectSV;

    private final ProgramElement body;

    private final String name = "init-array-creation";

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public SchemaVariable newObjectSV() {
        return newObjectSV;
    }

    public ProgramElement body() {
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

    public InitArrayCreation(SchemaVariable newObjectSV, ProgramElement body, @EqEx @Nullable PositionInfo positionInfo) {
        this.newObjectSV = Objects.requireNonNull(newObjectSV);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public InitArrayCreation(SchemaVariable newObjectSV, ProgramElement body) {
        this.newObjectSV = Objects.requireNonNull(newObjectSV);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public InitArrayCreation(InitArrayCreation other) {
        this(other.newObjectSV, other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof InitArrayCreation other))
            return null;
        cond = MatchHelper.match(newObjectSV, other.newObjectSV, cond);
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

    public InitArrayCreation withNewObjectSV(SchemaVariable newObjectSV) {
        return new InitArrayCreation(newObjectSV, body(), name(), positionInfo());
    }

    public InitArrayCreation withBody(ProgramElement body) {
        return new InitArrayCreation(newObjectSV(), body, name(), positionInfo());
    }

    public InitArrayCreation withPositionInfo(PositionInfo positionInfo) {
        return new InitArrayCreation(newObjectSV(), body(), name(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public SchemaVariable newObjectSV;

        @Nullable()
        public ProgramElement body;

        @Nullable()
        public PositionInfo positionInfo;

        public InitArrayCreation build() {
            return new InitArrayCreation(newObjectSV, body, positionInfo);
        }

        public Builder newObjectSV(SchemaVariable newObjectSV) {
            this.newObjectSV = newObjectSV;
            return this;
        }

        public Builder body(ProgramElement body) {
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
        b.newObjectSV = newObjectSV;
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof InitArrayCreation that))
            return false;
        return Objects.equals(newObjectSV, that.newObjectSV) && Objects.equals(body, that.body) && Objects.equals(name, that.name);
    }

    @Override()
    public String toString() {
        return "InitArrayCreation[newObjectSV=%s, body=%s, name=%s, positionInfo=%s]".formatted(newObjectSV, body, name, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(newObjectSV, body, name);
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
