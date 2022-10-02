package de.uka.ilkd.key.logic.origin;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Objects;

public class OriginRef {

    public static final Collection<OriginRef> EMPTY = new ArrayList<>();

    public final String File;

    public final int LineStart;
    public final int LineEnd;

    public final int PositionStart;
    public final int PositionEnd;

    public final OriginTermLabel.SpecType Type;

    public OriginRef(String file, int lineStart, int lineEnd, int positionStart, int positionEnd, OriginTermLabel.SpecType type) {
        File = file;
        LineStart = lineStart;
        LineEnd = lineEnd;
        PositionStart = positionStart;
        PositionEnd = positionEnd;
        Type = type;
    }

    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }

        final OriginRef cmp = (OriginRef) o;

        return Objects.equals(this.File, cmp.File) &&
                this.Type ==  cmp.Type &&
                this.LineStart ==  cmp.LineStart &&
                this.LineEnd ==  cmp.LineEnd &&
                this.PositionStart ==  cmp.PositionStart &&
                this.PositionEnd ==  cmp.PositionEnd;
    }

    private int hashcode = -1;

    @Override
    public final int hashCode(){
        if(hashcode == -1) {
            // compute into local variable first to be thread-safe.
            this.hashcode = computeHashCode();
        }
        return hashcode;
    }

    public int computeHashCode() {
        int hash = 0;
        hash += 7 * this.File.hashCode();
        hash += 7 * this.Type.hashCode();
        hash += 7 * this.LineStart;
        hash += 7 * this.LineEnd;
        hash += 7 * this.PositionStart;
        hash += 7 * this.PositionEnd;
        return hash;
    }

}
