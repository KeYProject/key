package de.uka.ilkd.key.speclang.njml;

public enum SpecMathMode {
    BIGINT, JAVA;

    public static SpecMathMode defaultMode() {
        return BIGINT;
    }
}
