package de.uka.ilkd.key.logic.origin;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

public class OriginRef {

    public final String File;

    public final int LineStart;
    public final int LineEnd;

    public final int ColumnStart;
    public final int ColumnEnd;

    public final OriginRefType Type;

    public final boolean IsBooleanTerm;
    public final boolean IsAtom;

    private String sourceStringCache = null;
    private boolean cached= false;

    public OriginRef(OriginRefType type, boolean isatom, boolean isbool) {
        this(null, 0, 0, 0, 0, type, isatom, isbool);
    }

    public OriginRef(String file, int lineStart, int lineEnd, int colStart, int colEnd, OriginRefType type, boolean isatom, boolean isbool) {
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

        IsAtom = isatom;
        IsBooleanTerm = isbool;
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

    public @Nonnull String sourceString() {
        if (!cached) {

            if (File != null) {

                try {
                    List<String> lines = Files.readAllLines(Path.of(fileURI()));

                    StringBuilder r = new StringBuilder();
                    for (int i = LineStart; i <= LineEnd; i++) {
                        if (i-1 < lines.size()) {
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
                    cached = true;
                } catch (IOException e) {
                    sourceStringCache = "";
                    cached = true;
                }
            } else {
                sourceStringCache = "";
                cached = true;
            }

        }


        return sourceStringCache;
    }

    private static String safeSubstring(String str, int start, int end) {
        start = Math.max(start, 0);
        end = Math.min(end, str.length());

        return str.substring(start, end);
    }

    @Override
    public String toString() {

        String flags = "[" + ( IsAtom ? "A" : " " ) + "|" + ( IsBooleanTerm ? "B" : " " ) + "]";

        String padType = String.format("%-17s", Type);

        String fileStr = "(no-src)";
        if (hasFile()) {

            String f = File;

            String fprefix = "";
            if (f.contains(":")) {
                int idx = f.indexOf(":");
                fprefix = f.substring(0, idx);
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

            fileStr = fprefix + main + ":" + line + " [" + pos + "]";

        }

        return flags + " " + padType + " || " + fileStr;
    }

    public OriginRef WithType(OriginRefType t) {
        return new OriginRef(File, LineStart, LineEnd, ColumnStart, ColumnEnd, t, IsAtom, IsBooleanTerm);
    }

    public OriginRef WithIsAtom(boolean a) {
        return new OriginRef(File, LineStart, LineEnd, ColumnStart, ColumnEnd, Type, a, IsBooleanTerm);
    }
}
