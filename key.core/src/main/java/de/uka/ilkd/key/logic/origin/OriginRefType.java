package de.uka.ilkd.key.logic.origin;

/**
 * List of OriginRefTypes for OriginRefs
 */
public enum OriginRefType {

    UNKNOWN("unknown"),
    JAVA_STMT("java_statement"),

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
    IMPLICIT_ENSURES_ASSIGNABLE("ensures_assignable"),

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
    LOOP_INITIALLYVALID_WELLFORMED("loop_initiallyvalid_wellformed"),

    LOOP_BODYPRESERVEDINV_WELLFORMED("loop_bodypreservesinvarriant_wellformed"),
    LOOP_BODYPRESERVEDINV_INVARIANT_BEFORE("loop_bodypreservesinvarriant_invariant_before"),
    LOOP_BODYPRESERVEDINV_INVARIANT_AFTER("loop_bodypreservesinvarriant_invariant_after"),
    LOOP_BODYPRESERVEDINV_ASSIGNABLE("loop_bodypreservesinvarriant_assignable"),
    LOOP_BODYPRESERVEDINV_VARIANT("loop_bodypreservesinvarriant_variant"),
    LOOP_BODYPRESERVEDINV_GUARD("loop_bodypreservesinvarriant_guard"),

    LOOP_USECASE_GUARD("loop_usecase_guard"),
    LOOP_USECASE_INVARIANT("loop_usecase_invariant"),
    LOOP_USECASE_WELLFORMED("loop_usecase_wellformed"),

    LOOP_ANONUPDATE("loop_anonupdate"),

    OPERATION_PRE_WELLFORMED("operation_pre_wellformed"),
    OPERATION_PRE_PRECONDITION("operation_pre_precondition"),
    OPERATION_PRE_MEASUREDBY("operation_pre_measuredby"),

    OPERATION_POST_WELLFORMED("operation_post_wellformed"),
    OPERATION_POST_SELFINVARIANT("operation_post_selfinvariant"),
    OPERATION_POST_ASSIGNABLE("operation_post_assignable"),
    OPERATION_POST_EXCNULL("operation_post_excnull"),

    OPERATION_EXC_WELLFORMED("operation_exc_wellformed"),
    OPERATION_EXC_SELFINVARIANT("operation_exc_selfinvariant"),
    OPERATION_EXC_ASSIGNABLE("operation_exc_assignable"),
    OPERATION_EXC_EXCNULL("operation_exc_excnull"),

    OPERATION_POSTCONDITION("operation_postcondition"),
    OPERATION_ANONUPDATE("operation_anonupdate"),
    OPERATION_ANONASSUMPTION("operation_anonassumption"),
    OPERATION_EXCNULL("operation_excnull"),
    OPERATION_SELFCREATED("operation_selfcreated");


    private final String name;

    OriginRefType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

    public boolean isRequires() {
        return     this == OriginRefType.JML_REQUIRES
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
                || this == OriginRefType.IMPLICIT_ENSURES_EXCNULL
                || this == OriginRefType.OPERATION_POST_EXCNULL
                || this == OriginRefType.OPERATION_EXC_EXCNULL;
    }
}
