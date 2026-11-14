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
public final class Comment extends JavaSourceElement implements JavaProgramElement {

    private final String text;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public String text() {
        return text;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Comment(String text, @EqEx @Nullable PositionInfo positionInfo) {
        this.text = Objects.requireNonNull(text);
        this.positionInfo = positionInfo;
    }

    public Comment(String text) {
        this.text = Objects.requireNonNull(text);
        this.positionInfo = null;
    }

    public Comment(Comment other) {
        this(other.text, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Comment other))
            return null;
        cond = MatchHelper.match(text, other.text, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Comment withText(String text) {
        return new Comment(text, positionInfo());
    }

    public Comment withPositionInfo(PositionInfo positionInfo) {
        return new Comment(text(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public String text;

        @Nullable()
        public PositionInfo positionInfo;

        public Comment build() {
            return new Comment(text, positionInfo);
        }

        public Builder text(String text) {
            this.text = text;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.text = text;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Comment that))
            return false;
        return Objects.equals(text, that.text);
    }

    @Override()
    public String toString() {
        return "Comment[text=%s, positionInfo=%s]".formatted(text, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(text);
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
