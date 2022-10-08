package de.uka.ilkd.key.logic.origin;

public enum OriginRefType {

    ACCESSIBLE("accessible"),
    ASSERT("assert"),
    ASSIGNABLE("assignable"),
    ASSUME("assume"),
    DECREASES("decreases"),
    MEASURED_BY("measured_by"),
    INVARIANT("invariant"),
    LOOP_INVARIANT("loop_invariant"),
    LOOP_INVARIANT_FREE("loop_invariant_free"),
    REQUIRES_FREE("requires_free"),
    ENSURES_FREE("ensures_free"),
    SIGNALS("signals"),
    SIGNALS_ONLY("signals_only"),
    BREAKS("breaks"),
    CONTINUES("continues"),
    RETURNS("returns"),

    REQUIRES("requires"), // @requires clause
    ENSURES("ensures"),   // @ensures clause

    ENSURES_IMPLICT("ensures_implicit");   // autom. generated ensures term

    private final String name;

    private OriginRefType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }
}
