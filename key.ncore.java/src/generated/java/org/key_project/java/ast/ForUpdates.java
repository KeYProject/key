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
public final class ForUpdates extends JavaSourceElement implements JavaProgramElement {

    private final ImmutableList<Expression> updates;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ImmutableList<Expression> updates() {
        return updates;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ForUpdates(ImmutableList<Expression> updates, @EqEx @Nullable PositionInfo positionInfo) {
        this.updates = Objects.requireNonNull(updates);
        this.positionInfo = positionInfo;
    }

    public ForUpdates(ImmutableList<Expression> updates) {
        this.updates = Objects.requireNonNull(updates);
        this.positionInfo = null;
    }

    public ForUpdates(ForUpdates other) {
        this(other.updates, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ForUpdates other))
            return null;
        cond = MatchHelper.match(updates, other.updates, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ForUpdates withUpdates(ImmutableList<Expression> updates) {
        return new ForUpdates(updates, positionInfo());
    }

    public ForUpdates withPositionInfo(PositionInfo positionInfo) {
        return new ForUpdates(updates(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<Expression> updates;

        @Nullable()
        public PositionInfo positionInfo;

        public ForUpdates build() {
            return new ForUpdates(updates, positionInfo);
        }

        public Builder updates(ImmutableList<Expression> updates) {
            this.updates = updates;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder updates(Expression updates) {
            if (this.updates == null)
                this.updates = new ArrayList<>();
            this.updates.add(updates);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.updates = updates;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ForUpdates that))
            return false;
        return Objects.equals(updates, that.updates);
    }

    @Override()
    public String toString() {
        return "ForUpdates[updates=%s, positionInfo=%s]".formatted(updates, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(updates);
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
