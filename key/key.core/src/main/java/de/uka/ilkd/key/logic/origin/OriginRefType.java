package de.uka.ilkd.key.logic.origin;

public enum OriginRefType {

    UNKNOWN("unknown"),

    JML_ACCESSIBLE("accessible"),
    JML_ASSERT("assert"),
    JML_ASSIGNABLE("assignable"),
    JML_ASSUME("assume"),
    JML_DECREASES("decreases"),
    JML_MEASURED_BY("measured_by"),
    JML_INVARIANT("invariant"),
    JML_LOOP_INVARIANT("loop_invariant"),
    JML_LOOP_INVARIANT_FREE("loop_invariant_free"),
    JML_SIGNALS("signals"),
    JML_SIGNALS_ONLY("signals_only"),
    JML_BREAKS("breaks"),
    JML_CONTINUES("continues"),
    JML_RETURNS("returns"),
    JML_REQUIRES("requires"),
    JML_REQUIRES_FREE("requires_free"),
    JML_ENSURES("ensures"),
    JML_ENSURES_FREE("ensures_free"),

    IMPLICIT_ENSURES_EXCNULL("ensures_exc_null"),
    IMPLICIT_ENSURES_SELFINVARIANT("ensures_self_invariant"),
    IMPLICIT_ENSURES_ASSIGNABLE("ensures_assignable_implicit"),

    IMPLICIT_REQUIRES_SELFNOTNULL("requires_self_not_null"),
    IMPLICIT_REQUIRES_SELFCREATED("requires_self_created"),
    IMPLICIT_REQUIRES_SELFEXACTINSTANCE("requires_self_exact_instance"),
    IMPLICIT_REQUIRES_PARAMSOK("requires_params_ok"),
    IMPLICIT_REQUIRES_MEASUREDBY_INITIAL("requires_measuredby_initial"),
    IMPLICIT_REQUIRES_WELLFORMEDHEAP("requires_wellformed_heap"),
    IMPLICIT_REQUIRES_SELFINVARIANT("requires_self_invariant"),
    IMPLICIT_REQUIRES_PARAM_NON_NULL("ensures_param_non_null"),

    IMPLICIT_SIGNALS_SELFINVARIANT("signals_self_invariant"),

    USER_INTERACTION("user_interaction"),

    LOOP_INITIALLYVALID_INVARIANT("loop_initiallyvalid_invariant"),
    LOOP_INITIALLYVALID_REACHABLE("loop_initiallyvalid_reachable");


    private final String name;

    private OriginRefType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

    public boolean isRequires() {
        return this == OriginRefType.JML_REQUIRES
                || this == OriginRefType.JML_REQUIRES_FREE
                || this == OriginRefType.IMPLICIT_REQUIRES_SELFINVARIANT
                || this == OriginRefType.IMPLICIT_REQUIRES_PARAMSOK
                || this == OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE
                || this == OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP
                || this == OriginRefType.IMPLICIT_REQUIRES_SELFCREATED
                || this == OriginRefType.IMPLICIT_REQUIRES_MEASUREDBY_INITIAL
                || this == OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL
                || this == OriginRefType.IMPLICIT_REQUIRES_PARAM_NON_NULL;
    }

    public boolean isEnsures() {
        return this == OriginRefType.JML_ENSURES
                || this == OriginRefType.JML_ENSURES_FREE
                || this == OriginRefType.IMPLICIT_ENSURES_SELFINVARIANT
                || this == OriginRefType.IMPLICIT_ENSURES_ASSIGNABLE
                || this == OriginRefType.IMPLICIT_ENSURES_EXCNULL;
    }

    public boolean isUserInteraction() {
        return this == OriginRefType.USER_INTERACTION;
    }

}
