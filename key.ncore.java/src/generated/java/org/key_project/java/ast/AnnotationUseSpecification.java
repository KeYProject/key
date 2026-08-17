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
public final class AnnotationUseSpecification extends JavaSourceElement implements Modifier {

    private final TypeReference tr;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public TypeReference tr() {
        return tr;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public AnnotationUseSpecification(TypeReference tr, @EqEx @Nullable PositionInfo positionInfo) {
        this.tr = Objects.requireNonNull(tr);
        this.positionInfo = positionInfo;
    }

    public AnnotationUseSpecification(TypeReference tr) {
        this.tr = Objects.requireNonNull(tr);
        this.positionInfo = null;
    }

    public AnnotationUseSpecification(AnnotationUseSpecification other) {
        this(other.tr, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof AnnotationUseSpecification other))
            return null;
        cond = MatchHelper.match(tr, other.tr, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public AnnotationUseSpecification withTr(TypeReference tr) {
        return new AnnotationUseSpecification(tr, positionInfo());
    }

    public AnnotationUseSpecification withPositionInfo(PositionInfo positionInfo) {
        return new AnnotationUseSpecification(tr(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public TypeReference tr;

        @Nullable()
        public PositionInfo positionInfo;

        public AnnotationUseSpecification build() {
            return new AnnotationUseSpecification(tr, positionInfo);
        }

        public Builder tr(TypeReference tr) {
            this.tr = tr;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.tr = tr;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof AnnotationUseSpecification that))
            return false;
        return Objects.equals(tr, that.tr);
    }

    @Override()
    public String toString() {
        return "AnnotationUseSpecification[tr=%s, positionInfo=%s]".formatted(tr, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(tr);
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
