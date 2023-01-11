package de.uka.ilkd.key.speclang.njml;

/**
 * Spec math modes
 */
public enum SpecMathMode {
    /** Bigint arithmetic */
    BIGINT,
    /** Java semantics */
    JAVA,
    /** Bigint arithmetic with checked overflows */
    SAFE;

    /**
     * Default spec math mode
     */
    public static SpecMathMode defaultMode() {
        return BIGINT;
    }
}
