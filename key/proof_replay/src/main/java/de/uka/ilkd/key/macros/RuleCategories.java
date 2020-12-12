package de.uka.ilkd.key.macros;

public class RuleCategories {
    // Note: arrays contain not all rules to prevent proof cycles with no progression

    public static final String[] FIRST_ORDER_RULES = {
        "allLeft",
        "exRight",
        "allLeftHide",
        "exRightHide",
        "instAll",
        "instEx",
        "allRight",
        "exLeft",
        "all_unused",
        "ex_unused",
        "eqClose",
        "eqSymm",
        //"make_insert_eq",
        //"make_insert_eq_nonrigid",
        "insert_eq_all",
        "apply_subst",
        "apply_subst_for",
        "subst_to_eq_for",
        "applyEq",
        "applyEqReverse",
        "applyEqRigid",
        "pullOut",
        //"eqTermCut",
        "equalUnique"
    };

    public static final String[] PROPOSITIONAL_RULES = {
        "close",
        "closeAntec",
        "closeFalse",
        "closeTrue",
        "replace_known_left",
        "replace_known_right",
        "true_left",
        "false_right",
        "notLeft",
        "notRight",
        "impLeft",
        "doubleImpLeft",
        "impRight",
        "andLeft",
        "andRight",
        "orLeft",
        "orRight",
        "equiv_left",
        "equiv_right",
        "rotate_and",
        "rotate_or",
        "insert_eqv_once_lr",
        "insert_eqv_once_rl",
        "insert_eqv_lr",
        "insert_eqv_rl",
        "double_not",
        "concrete_not_1",
        "concrete_not_2",
        "concrete_impl_1",
        "concrete_impl_2",
        "concrete_impl_3",
        "concrete_impl_4",
        "concrete_and_1",
        "concrete_and_2",
        "concrete_and_3",
        "concrete_and_4",
        "concrete_or_1",
        "concrete_or_2",
        "concrete_or_3",
        "concrete_or_4",
        "concrete_or_5",
        "concrete_eq_2",
        "concrete_eq_3",
        "concrete_eq_4",
        "cut"
    };

    public final static String[] BOOLEAN_RULES = {
        "boolean_equal",
        "boolean_equal_2",
        "boolean_not_equal_1",
        "boolean_not_equal_2",
        //"true_to_not_false",
        "false_to_not_true",
        "boolean_true_commute",
        "boolean_false_commute",
        "eq_bool",
        "all_bool",
        "apply_eq_boolean",
        "apply_eq_boolean_2",
        "apply_eq_boolean_rigid",
        "apply_eq_boolean_rigid_2"
    };

    private RuleCategories() {
    }
}
