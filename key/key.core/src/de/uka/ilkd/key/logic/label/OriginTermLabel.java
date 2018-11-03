package de.uka.ilkd.key.logic.label;

import java.nio.file.Paths;

import de.uka.ilkd.key.logic.Name;

public class OriginTermLabel implements TermLabel {

    public final static Name NAME = new Name("Origin");

    private Origin origin;

    public OriginTermLabel(SpecType specType, String file, int line) {
        // Just the file name, without any directories
        String filename = Paths.get(file).getFileName().toString();

        this.origin = new Origin(specType, filename, line);
    }

    @Override
    public String toString() {
        return "" + NAME + "(" + origin + ")";
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        if (i == 0) {
            return origin; 
        } else {
            return null;
        }
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    public static class Origin implements Comparable<Origin> {

        public final SpecType specType;
        public final String fileName;
        public final int line;

        public Origin(SpecType specType, String fileName, int line) {
            this.specType = specType;
            this.fileName = fileName;
            this.line = line;
        }

        @Override
        public String toString() {
            return "(" + specType + ", (" + fileName + ", " + line + "))";
        }

        @Override
        public int compareTo(Origin other) {
            int result = specType.toString().compareTo(other.specType.toString());

            if (result == 0) {
                result = fileName.compareTo(other.fileName);

                if (result == 0) {
                    result = Integer.compare(line, other.line);
                }
            }

            return result;
        }
    }

    public static enum SpecType {
        
        ACCESSIBLE("accessible"),
        ASSIGNABLE("assignable"),
        DECREASES("decreases"),
        MEASURED_BY("measured_by"),
        CLASS_INVARIANT("invariant"),
        LOOP_INVARIANT("loop_invariant"),
        LOOP_INVARIANT_FREE("loop_invariant_free"),
        REQUIRES("requires"),
        REQUIRES_FREE("requires_free"),
        ENSURES("ensures"),
        ENSURES_FREE("ensures_free"),
        SIGNALS("signals"),
        SIGNALS_ONLY("signals_only"),
        BREAKS("breaks"),
        CONTINUES("continues"),
        RETURNS("returns");

        private String name;

        private SpecType(String name) {
            this.name = name;
        }

        @Override
        public String toString() {
            return name;
        }
    }
}
