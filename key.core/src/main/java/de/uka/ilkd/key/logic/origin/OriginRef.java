package de.uka.ilkd.key.logic.origin;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import org.jspecify.annotations.NonNull;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * This class represents the origin of a term
 *
 * The specific type of origin is encoded in the OriginRefType.
 * If the origins is from a JML string in an input file the File/LineStart/LineEnd/ColumnStart/ColumnEnd fields are set.
 */
public class OriginRef {

    public final String File;

    public final int LineStart;
    public final int LineEnd;

    public final int ColumnStart;
    public final int ColumnEnd;

    public final OriginRefType Type;

    public final Term SourceTerm;

    private String sourceStringCache = null;
    private boolean sourceStringCached = false;

    private Boolean isAtomCache = null;
    private Boolean isBooleanTermCache = null;

    public OriginRef(OriginRefType type, Term t) {
        this(null, 0, 0, 0, 0, type, t);
    }

    public OriginRef(String file, int lineStart, int lineEnd, int colStart, int colEnd,
            OriginRefType type, Term term) {
        if (file == null || file.isEmpty() || file.equals("no file") || file.equals("<unknown>") || file.equals("UNKNOWN://unknown")) {
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
        SourceTerm = term;
    }

    @Override
    public boolean equals(Object o) {
        if (o.getClass() != this.getClass())
            return false;

        final OriginRef cmp = (OriginRef) o;

        return this.Type == cmp.Type && this.LineStart == cmp.LineStart
                && this.LineEnd == cmp.LineEnd && this.ColumnStart == cmp.ColumnStart
                && this.ColumnEnd == cmp.ColumnEnd
                && Objects.equals(this.SourceTerm, cmp.SourceTerm);
    }

    public boolean equalsModSource(OriginRef o) {
        if (o.getClass() != this.getClass())
            return false;

        return this.Type == o.Type &&
               this.LineStart == o.LineStart &&
               this.LineEnd == o.LineEnd &&
               this.ColumnStart == o.ColumnStart &&
               this.ColumnEnd == o.ColumnEnd;
    }

    private int hashcode = -1;

    @Override
    public final int hashCode() {
        if (hashcode == -1) {
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
        hash += 7 * (this.SourceTerm == null ? 0 : this.SourceTerm.hashCode());
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

    public @NonNull Optional<String> sourceString() {
        if (!sourceStringCached) {

            if (File != null) {

                try {
                    List<String> lines = Files.readAllLines(Path.of(fileURI()));

                    StringBuilder r = new StringBuilder();
                    for (int i = LineStart; i <= LineEnd; i++) {
                        if (i-1 >= 0 && i - 1 < lines.size()) {
                            String line = lines.get(i - 1);
                            if (i == LineStart && i == LineEnd) {
                                r.append(safeSubstring(line, ColumnStart, ColumnEnd));
                            } else if (i == LineStart) {
                                r.append(safeSubstring(line, ColumnStart, line.length()));
                                r.append("\n");
                            } else if (i == LineEnd) {
                                r.append(safeSubstring(line, 0, ColumnEnd));
                            } else {
                                r.append(line);
                                r.append("\n");
                            }
                        }
                    }
                    sourceStringCache = r.toString();
                    sourceStringCached = true;
                } catch (IOException e) {
                    sourceStringCache = null;
                    sourceStringCached = true;
                }
            } else {
                sourceStringCache = null;
                sourceStringCached = true;
            }

        }

        return (sourceStringCache == null) ? Optional.empty() : Optional.of(sourceStringCache);
    }

    private static String safeSubstring(String str, int start, int end) {
        start = Math.max(start, 0);
        end = Math.min(end, str.length());

        if (start >= end) {
            return "";
        }

        return str.substring(start, end);
    }

    @Override
    public String toString() {
        return String.format("%-17s", Type) + " || " + sourcetoString();
    }

    public String sourcetoString() {

        String fileStr = "(no-src)";
        if (hasFile()) {

            String f = File;

            String fprefix = "";
            if (f.contains(":")) {
                int idx = f.indexOf(":");
                fprefix = f.substring(0, idx);
                f = f.substring(idx + 1);
            }
            String main = f;
            if (f.contains("/")) {
                main = f.substring(f.lastIndexOf("/") + 1);
            } else if (f.contains("\\")) {
                main = f.substring(f.lastIndexOf("\\") + 1);
            }

            String line = "" + LineStart;
            if (LineStart != LineEnd) {
                line = LineStart + "-" + LineEnd;
            }

            String pos = ColumnStart + ".." + ColumnEnd;

            fileStr = fprefix + main + ":" + line + " [" + pos + "]";

        }

        return fileStr;
    }

    public OriginRef WithType(OriginRefType t) {
        return new OriginRef(File, LineStart, LineEnd, ColumnStart, ColumnEnd, t, SourceTerm);
    }

    public OriginRef WithoutFile() {
        return new OriginRef(null, 0, 0, 0, 0, Type, SourceTerm);
    }

    public boolean isAtom() {
        if (isAtomCache == null) {
            isAtomCache = calculateIsAtom(SourceTerm);
        }

        return isAtomCache;
    }

    public boolean isBooleanTerm() {
        if (isBooleanTermCache == null) {
            isBooleanTermCache = calculateIsBooleanTerm(SourceTerm);
        }

        return isBooleanTermCache;
    }

    private static boolean calculateIsAtom(Term t) {
        if (t == null) return false;

        if (!calculateIsBooleanTerm(t)) return false;

        if (hasAtomChildren(t)) return false;

        return true;
    }

    private static boolean calculateIsBooleanTerm(Term t) {
        if (t == null) return false;

        return t.op().sort(t.subs().toArray(new Sort[0])) == JavaDLTheory.FORMULA; //TODO is this right?
    }

    private static boolean hasAtomChildren(Term t) {
        for (var sub: t.subs()) {
            if (calculateIsAtom(sub)) return true;
            if (hasAtomChildren(sub)) return true;
        }

        return false;
    }

    public OriginRef copy() {
        return new OriginRef(File, LineStart, LineEnd, ColumnStart, ColumnEnd, Type, SourceTerm);
    }

    public static OriginRef fromStatement(SourceElement stmt) {
        var pi = stmt.getPositionInfo();
        return new OriginRef(
                pi.getURI().toString(),
                pi.getStartPosition().line(), pi.getEndPosition().line(),
                pi.getStartPosition().column(), pi.getEndPosition().column(),
                OriginRefType.JAVA_STMT, null);
    }
}
