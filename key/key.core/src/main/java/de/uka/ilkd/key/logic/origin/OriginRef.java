package de.uka.ilkd.key.logic.origin;

import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.net.URI;

public class OriginRef {

    public static final ImmutableSet<OriginRef> EMPTY                       = ImmutableSet.empty();
    public static final ImmutableSet<OriginRef> ENSURES_EXCNULL             = ImmutableSet.singleton(new OriginRef(OriginRefType.ENSURES_IMPLICT));
    public static final ImmutableSet<OriginRef> ENSURES_SELFINVARIANT       = ImmutableSet.singleton(new OriginRef(OriginRefType.ENSURES_IMPLICT));
    public static final ImmutableSet<OriginRef> ENSURES_ASSIGNABLE_IMPLICIT = ImmutableSet.singleton(new OriginRef(OriginRefType.ENSURES_IMPLICT));
    public static final ImmutableSet<OriginRef> REQUIRES_SELFNOTNULL        = ImmutableSet.singleton(new OriginRef(OriginRefType.REQUIRES_IMPLICT));
    public static final ImmutableSet<OriginRef> REQUIRES_SELFCREATED        = ImmutableSet.singleton(new OriginRef(OriginRefType.REQUIRES_IMPLICT));
    public static final ImmutableSet<OriginRef> REQUIRES_SELFEXACTTYPE      = ImmutableSet.singleton(new OriginRef(OriginRefType.REQUIRES_IMPLICT));
    public static final ImmutableSet<OriginRef> REQUIRES_PARAMSOK           = ImmutableSet.singleton(new OriginRef(OriginRefType.REQUIRES_IMPLICT));
    public static final ImmutableSet<OriginRef> REQUIRES_MEASUREDBY_INITIAL = ImmutableSet.singleton(new OriginRef(OriginRefType.REQUIRES_IMPLICT));
    public static final ImmutableSet<OriginRef> REQUIRES_WELLFORMEDHEAP     = ImmutableSet.singleton(new OriginRef(OriginRefType.REQUIRES_IMPLICT));
    public static final ImmutableSet<OriginRef> REQUIRES_SELFINVARIANT      = ImmutableSet.singleton(new OriginRef(OriginRefType.REQUIRES_IMPLICT));
    public static final ImmutableSet<OriginRef> SIGNALS_SELFINVARIANT       = ImmutableSet.singleton(new OriginRef(OriginRefType.SIGNALS_IMPLICT));

    public final String File;

    public final int LineStart;
    public final int LineEnd;

    public final int ColumnStart;
    public final int ColumnEnd;

    public final OriginRefType Type;

    public OriginRef(OriginRefType type) {
        this(null, 0, 0, 0, 0, type);
    }

    public OriginRef(String file, int lineStart, int lineEnd, int colStart, int colEnd, OriginRefType type) {
        if (file == null || file.isEmpty() || file.equals("no file") || file.equals("<unknown>")) {
            File = null;
            LineStart = 0;
            LineEnd = 0;
            ColumnStart = 0;
            ColumnEnd = 0;
        } else {
            File = file;
            LineStart = lineStart;
            LineEnd = lineEnd;
            ColumnStart = colStart;
            ColumnEnd = colEnd;
        }

        Type = type;
    }

    @Override
    public boolean equals(Object o) {
        if (o.getClass() != this.getClass()) return false;

        final OriginRef cmp = (OriginRef) o;

        return this.Type        ==  cmp.Type        &&
               this.LineStart   ==  cmp.LineStart   &&
               this.LineEnd     ==  cmp.LineEnd     &&
               this.ColumnStart ==  cmp.ColumnStart &&
               this.ColumnEnd   ==  cmp.ColumnEnd;
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
        hash += 7 * (this.File == null ? 0 : this.File.hashCode());
        hash += 7 * this.Type.hashCode();
        hash += 7 * this.LineStart;
        hash += 7 * this.LineEnd;
        hash += 7 * this.ColumnStart;
        hash += 7 * this.ColumnEnd;
        return hash;
    }

    public URI fileURI() {
        if (File == null) {
            return null;
        }
        if (File.startsWith("file:")) {
            return new File(File.substring("file:".length())).toURI();
        } else {
            return new File(File).toURI();
        }
    }

    public boolean hasFile() {
        return (File != null);
    }

    @Override
    public String toString() {
        if (hasFile()) {

            String f = File;

            String prefix = "";
            if (f.contains(":")) {
                int idx = f.indexOf(":");
                prefix = f.substring(0, idx);
                f = f.substring(idx+1);
            }
            String main = f;
            if (f.contains("/")) {
                main = f.substring(f.lastIndexOf("/")+1);
            } else if (f.contains("\\")) {
                main = f.substring(f.lastIndexOf("\\")+1);
            }

            String line = ""+LineStart;
            if (LineStart != LineEnd) {
                line = LineStart+"-"+LineEnd;
            }

            String pos = ""+ ColumnStart;
            if (ColumnStart != ColumnEnd) {
                pos = ColumnStart +"-"+ ColumnEnd;
            }

            return String.format("%-17s", Type) + " || " + prefix + main + ":" + line + " [" + pos + "]";

        } else {

            return String.format("%-17s", Type) + " || (no-src)";

        }
    }
}
